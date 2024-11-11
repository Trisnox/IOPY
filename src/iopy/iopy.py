import io
import os
import pathlib
import struct
import zlib
from datetime import datetime

ZIP_LOCAL_HEADER_SIGNATURE = b'PK\x03\x04'
ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE = b'PK\x01\x02'
ZIP_DATA_DESCRIPTOR_HEADER_SIGNATURE = b'PK\x07\x08'
ZIP_END_CENTRAL_HEADER_SIGNATURE = b'PK\x05\x06'


class ZipCrypto():
    """
    Slightly modified version, only needed to specifically decrypt a compressed bytes
    since I can't pass ZipFile class or something to access the mod_time
    https://github.com/danifus/pyzipper/blob/master/pyzipper/zipfile.py#L875-L937

    PKWARE Encryption Decrypter

    ZIP supports a password-based form of encryption. Even though known
    plaintext attacks have been found against it, it is still useful
    to be able to get data out of such a file.

    Usage:
        zd = ZipCrypto(mypwd)
        plain_bytes = zd.decrypt(encrypted_bytes)

        zd = ZipCrypto(mypwd)
        encrypted_bytes = zd.encrypt(plain_bytes)
    """

    encryption_header_length = 12

    def __init__(self, pwd):

        def _gen_crc(crc):
            for j in range(8):
                if crc & 1:
                    crc = (crc >> 1) ^ 0xEDB88320
                else:
                    crc >>= 1
            return crc

        self.key0 = 305419896
        self.key1 = 591751049
        self.key2 = 878082192

        self.crctable = list(map(_gen_crc, range(256)))

        for p in pwd:
            self.update_keys(p)

    def crc32(self, ch, crc):
        """Compute the CRC32 primitive on one byte."""
        return (crc >> 8) ^ self.crctable[(crc ^ ch) & 0xFF]

    def update_keys(self, c):
        self.key0 = self.crc32(c, self.key0)
        self.key1 = (self.key1 + (self.key0 & 0xFF)) & 0xFFFFFFFF
        self.key1 = (self.key1 * 134775813 + 1) & 0xFFFFFFFF
        self.key2 = self.crc32(self.key1 >> 24, self.key2)

    def decrypt(self, data):
        """Decrypt a bytes object."""
        result = bytearray()
        append = result.append
        for c in data:
            k = self.key2 | 2
            c ^= ((k * (k ^ 1)) >> 8) & 0xFF
            self.update_keys(c)
            append(c)
        return bytes(result)

    def encrypt(self, data: bytes) -> bytes:
        """
        Encrypt bytes data.
        """
        # I really wish someone did an example code on this because I don't understand shit about programming or algorithm.
        # pyzipper lacks documentation, and I can't seem find the source code to encrypt bytes (probably because no one uses
        # ZipCrypto Encryption for obvious reason)
        # But anyways, I managed it, somehow...
        result = bytearray()
        for byte in data:
            key = (self.key2 | 2) & 0xFFFF
            val = ((key * (key ^ 1)) >> 8) & 0xFF
            encrypted_byte = byte ^ val
            self.update_keys(byte)
            result.append(encrypted_byte)
        return bytes(result)

class IOP():
    """
    Class to deconstruct or construct .iop headers. This class is used to obtain the file information
    through headers and returns it as a class object for convenience.

    This class only provide a single file entry, IOPY(...) is the one that handles entries to construct/deconstruct .iop file

    Attributes:
        entry: class: `bytes` type: `args`
            Bytes of single file entry

        filename: class: `str` type: `args`
            If provided, this will construct instead of deconstructing

        encrypted: class: `bool` type: `args`
            If set to `True`, it will generate Data Descriptor header as well. Ignored for deconstructing

        is_last: class: `bool` type: `kwargs`
            If this set to `True`, then End of Central Directory will be generated. Defaults to False

        mod_time: class: `int` type: `kwargs`
            16-bit int representation of modified time (hour, minute, second). Ignored for deconstructing

        mod_date: class: `int` type: `kwargs`
            16-bit int representation of modifited date (year, month, day). Ignored for deconstructing

        crc32: class: `int` type: `kwargs`
            CRC32 of the file. Ignored for for deconstructing

        uncompressed_size: class `int` type: `kwags`
            File size of uncompressed data. Ignored for deconstructing

        central_offset: class: `int` type: `kwargs`
            Number of bytes offset for the first central header. Only used if `is_last` is `True`. Ignored for deconstructing

        central_count: class: `int` type: `kwargs`
            Total count of central headers inside file. Only used if `is_last` is `True`. Ignored for deconstructing
        
        relative_offset: class: `int` type: `kwargs`
            The relative offset of local file header for this file entry. Ignored for deconstructing
    """
    def __init__(self, entry:bytes, filename = '', encrypted = False, **kwargs):
        self.ENTRY = entry
        self.ENCRYPTED = encrypted
        self.IS_DIR = False
        self.IS_LAST = kwargs.get('is_last', False)
        self.FILENAME_BASE = ''

        self.HEADERS = {}
        self.VERSION = 0
        self.FLAGS = 0
        self.METHOD = 0
        self.MOD_TIME = kwargs.get('mod_time', 0)
        self.MOD_DATE = kwargs.get('mod_date', 0)
        self.CRC32 = kwargs.get('crc32', 0)
        self.COMPRESSED_SIZE = 0
        self.UNCOMPRESSED_SIZE = kwargs.get('uncompressed_size', 0)
        self.EXTRA = 0
        self.FILENAME = filename
        self.FILENAME_LENGTH = 0
        self.EXTRA_FIELD = ''
        self.VERSION_BY = 0
        self.COMMENT_LENGTH = 0
        self.DISK_NUMBER = 0
        self.INTERNAL_ATTRIBUTES = 0
        self.EXTERNAL_ATTRIBUTES = 0
        self.RELATIVE_OFFSET = kwargs.get('relative_offset', 0)
        self.COMMENT = ''

        self.ENTRY_BYTES = None

        if not filename:
            self.__process_deconstruct()
        else:
            self.__process_construct(kwargs.get('central_offset', 0), kwargs.get('central_count', 0))

    def __filename_base(self):
        """
        Function to separate base filename and its full path
        """
        return os.path.basename(self.FILENAME)

    def __filename_length(self):
        return len(self.FILENAME)

    def __entry_bytes(self):
        return self.ENTRY[0][30 + self.FILENAME_LENGTH : 30 + self.FILENAME_LENGTH + self.COMPRESSED_SIZE]

    def __process_construct(self, central_offset, central_count):
        """
        Function to construct .iop headers.

        Called upon init, does not return anything, but rather stores them inside self.HEADERS variable

        self.HEADERS contains:
            local: Always available
            cdfh: Central Directory, if this file is not a directory
            decriptor: If this file was encrypted
            eocd: End of Central Directory, if this was the last entry of the file or directory
        """
        self.IS_DIR = not isinstance(self.ENTRY, bytes)

        self.VERSION = len(self.FILENAME)
        self.FLAGS = 0
        self.METHOD = 8
        self.COMPRESSED_SIZE = 0
        self.FILENAME_LENGTH = 20
        self.EXTRA_FIELD = 0
        self.EXTERNAL_ATTRIBUTES = 2176057376 # file

        cdfh_filename_length = 20
        cdfh_version_by = 0
        cdfh_extra_field = 20

        # These variable are used for encrypted/directory headers, since they return 0 on anywhere else but data descriptor
        method = self.METHOD
        flags = self.FLAGS
        cdfh_flags = 0
        crc32 = self.CRC32
        compressed_size = self.COMPRESSED_SIZE
        uncompressed_size = self.UNCOMPRESSED_SIZE
        filename_length = self.FILENAME_LENGTH
        extra_field = self.EXTRA_FIELD

        if self.IS_DIR:
            method = 0
            filename_length = 10
            cdfh_extra_field = 10
            self.EXTERNAL_ATTRIBUTES = 1107099664 # directory
        else:
            self.COMPRESSED_SIZE = len(self.ENTRY)
            compressed_size = self.COMPRESSED_SIZE

        if self.ENCRYPTED and not self.IS_DIR:
            flags = 0
            cdfh_flags = 9
            crc32 = 0
            compressed_size = 0
            uncompressed_size = 0
            extra_field = 9
        
        self.HEADERS['local'] = [int.from_bytes(ZIP_LOCAL_HEADER_SIGNATURE, 'little'), self.VERSION, flags, method,
                                 self.MOD_TIME, self.MOD_DATE, crc32, compressed_size, uncompressed_size,
                                 filename_length, extra_field]
        
        if self.ENCRYPTED and not self.IS_DIR:
            self.HEADERS['descriptor'] = [int.from_bytes(ZIP_DATA_DESCRIPTOR_HEADER_SIGNATURE, 'little'), self.CRC32, self.COMPRESSED_SIZE, self.UNCOMPRESSED_SIZE]
        
        self.HEADERS['cdfh'] = [int.from_bytes(ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE, 'little'), self.VERSION, cdfh_version_by, cdfh_flags, method,
                                self.MOD_TIME, self.MOD_DATE, self.CRC32, self.COMPRESSED_SIZE, self.UNCOMPRESSED_SIZE, cdfh_filename_length,
                                cdfh_extra_field, 0, self.DISK_NUMBER, self.INTERNAL_ATTRIBUTES,
                                self.EXTERNAL_ATTRIBUTES, self.RELATIVE_OFFSET]

        if not self.IS_LAST:
            return
        
        self.HEADERS['eocd'] = [int.from_bytes(ZIP_END_CENTRAL_HEADER_SIGNATURE, 'little'), 0, 0, central_count, central_count, 46+self.VERSION,
                                central_offset, self.COMMENT_LENGTH]

    def __process_deconstruct(self):
        """
        Function to deconstruct .iop headers.
        """
        # Local file header
        signature, self.VERSION, flags, self.METHOD, self.MOD_TIME, self.MOD_DATE, self.CRC32, \
        compressed_size, self.UNCOMPRESSED_SIZE, filename_length, extra_field = \
            struct.unpack('<IHHHHHIIIHH', self.ENTRY[0][:30])

        self.HEADERS['local'] = [signature, self.VERSION, flags, self.METHOD, self.MOD_TIME, self.MOD_DATE, self.CRC32,
                                 compressed_size, self.UNCOMPRESSED_SIZE, filename_length, extra_field]

        # Encrypted files will have some of their headers resulting in 0 or NUL, this appears to be a behaviour of ZipCrypto
        # encryption, though files encrypted using 7zip software does not behave the same like how ZipArchive (Artpol) does
        # I am unsure if that's how it should've looked like or not
        #
        # filename_len will also always resulted in 20, or 10 if it was directory, regardless of their actual length,
        # this behaviour is exclusive to .iop files only
        # It also appears that they swap the flags with extra_len, hence why this checks for extra_len instead of flags
        if extra_field != 0 and flags == 0:
            self.ENCRYPTED = True
            self.FLAGS = extra_field
            self.EXTRA_FIELD = flags
        else:
            self.ENCRYPTED = False

        # Since we don't know the actual filename length, we need to iterate it ourselves
        # It will continue to read bytes until a valid format has recognized
        # known_formats = ['cfg', 'ini', 'xml', 'txt', 'ani', 'msh', 'skl', 'cms', 'edg', 'dat', 'rar', 'dds', 'wav', 'lsc']
        # filename_temp = b''
        # appearantly iterating through bytes returns as an integer
        # https://stackoverflow.com/questions/14267452/iterate-over-individual-bytes-in-python-3
        #
        # If the script attempt to iterate through huge file, this will cause it to stuck for an indefinite amount of time
        # for x in [self.ENTRY[30:][i:i+1] for i in range(len(self.ENTRY[30:]))]:
        # Below is previous solution, which is to limit the iteration by 255 char since that's the longest possible
        # filename for windows.
        # for x in [self.ENTRY[30:285][i:i+1] for i in range(len(self.ENTRY[30:285]))]:
        # This one is probably the most efficient solution, which is to convert the int back to the bytes as we go
        #
        # Note:
        # This doesn't work if the filename length is less or equal to 4 (for directories)
        # for x in self.ENTRY[30:]:
        #     x = x.to_bytes(1, sys.byteorder)
        #     filename_temp += x
        #     if len(filename_temp) < 4:
        #         continue

        #     if filename_temp[-4:][0] == 46: # this is literal '.'
        #         if filename_temp[-3:].decode('utf-8') in known_formats:
        #             self.FILENAME = filename_temp.decode('utf-8')
        #         else:
        #             # debug purposes if Lost Saga ever pass a new file format into their archive
        #             print('unknown file format is passed, continue proceeding. File: ', filename_temp)
        #             self.FILENAME = filename_temp.decode('utf-8')
        #         break

        # New discovery, version is actually the filename length, I just had to find it out the hard way
        self.FILENAME = self.ENTRY[0][30:30+self.VERSION].decode('utf-8')

        # if filename_temp[-1] == 47: # this is literal '/'
        if self.FILENAME[-1] == '/':
            self.IS_DIR = True
            # self.FILENAME = filename_temp.decode('utf-8')
        # elif not self.FILENAME:
            # raise RuntimeError('Iteration fails to find filename within 255 byte range')
            # raise RuntimeError('Attempting to iterate through file with no format.')

        self.FILENAME_BASE = self.__filename_base()
        self.FILENAME_LENGTH = self.__filename_length()

        # Central directory file header
        # CDFH = self.ENTRY.split(ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE) # redundant due to splitting already done on IOPY()
        signature, self.VERSION_BY, self.VERSION, self.FLAGS, self.METHOD, mod_time, mod_date, \
        self.CRC32, self.COMPRESSED_SIZE, self.UNCOMPRESSED_SIZE, filename_length, extra_field, \
        file_comment_length, self.DISK_NUMBER, self.INTERNAL_ATTRIBUTES, self.EXTERNAL_ATTRIBUTES, \
        self.RELATIVE_OFFSET = struct.unpack('<IHHHHHHIIIHHHHHII', self.ENTRY[1][:46])

        # The signature is converted into int for the sake of consistency
        self.HEADERS['cdfh'] = [signature, self.VERSION_BY, self.VERSION, self.FLAGS, self.METHOD,
                                mod_time, mod_date, self.CRC32, self.COMPRESSED_SIZE, self.UNCOMPRESSED_SIZE, filename_length,
                                extra_field, file_comment_length, self.DISK_NUMBER, self.INTERNAL_ATTRIBUTES,
                                self.EXTERNAL_ATTRIBUTES, self.RELATIVE_OFFSET]

        # Data descriptor
        # Appearantly compressed size and uncompressed size only provided on data descriptor
        # if the file was encrypted, otherwise they appear at local file header/central directory
        if self.ENCRYPTED and not self.IS_DIR:
            signature, self.CRC32, self.COMPRESSED_SIZE, self.UNCOMPRESSED_SIZE = \
            struct.unpack('<IIII', self.ENTRY[0][-16:])

            self.HEADERS['descriptor'] = [signature, self.CRC32,
                                          self.COMPRESSED_SIZE, self.UNCOMPRESSED_SIZE]

        self.ENTRY_BYTES = self.__entry_bytes()

        if not self.IS_LAST:
            return
        # End of central directory
        # Not really needed, but it's nice to have a complete data or to debug/compare them
        signature, number_disk, central_offset_disk, central_num_disk, central_num_total, central_size, \
        central_offset, comment_len = struct.unpack('<IHHHHIIH', self.ENTRY[2][:22])

        self.HEADERS['eocd'] = [signature, number_disk, central_offset_disk, central_num_disk, central_num_total, central_size,
                                central_offset, comment_len]

class IOPY():
    """
    Class to deconstruct or construct .iop files. A prorietary file format used by Lost Saga.

    .iop are similar to zip files, but they're slightly modifed that it cannot be open with other zip programs.

    This class only accept entry like this ([local header], [file entry], [descriptor (if any)], [central header],
    [end header (only for last entry)])

    Attributes:
        file: class: `str` Type: `args`\n
            The location of .iop file. If this file is an .iop, it will deconstruct it, otherwise it will be treated
            as constructing .iop file.
        iop_filename: class: `str`: `kwargs`\n
            Filename that will be used for generated archive file. If not provided, then the file/folder name will be used
            for the archive name instead. Ignored for deconstructing
        dir: class: `str` Type: `kwargs`\n
            Directory used to extract files into. Defaults to current folder. Ignored for constructing, it will generate
            file on current directory
        include_dir: class: `bool` Type: `kwargs`\n
            Wherever to include directories (if any) when extracting the file(s). Defaults to `True`. Ignored for constructing
        password: class: `str`|`Nonetype` Type: `kwargs`\n
            Used to determine password used for .iop files, each region have different password. Defaults to kr.
            If set to `None`, then encryption will not be used, will cause error for decryption
        bytes_io: class: `bool` Type: `kwargs`\n
            If set to `True`, then extract function will return bytesIO instead of saving the file. Defaults to `False`.
        silent: class: `bool` Type: `kwargs`\n
            If set to `True`, then the class will not print the saved filename. Defaults to True
    """
    # I'll be honest, this is no different than rewriting Zipfile/pyzipper code, tbh it could've been much
    # easier if I were to modify the .iop header so that zip programs can read them, using Zipfile/pyzipper to extract them,
    # then, modify the headers so that the .iop can be read by the game and IOPManager program.
    # But, pyzipper isn't capable of editing headers, and most zip program/modules doesn't seem capable of raw deflate compression
    # (or do they? 7-zip doesn't seem to compress text files, whereas ZipArchive/IOPManager would compress them regardless).
    # Another reason is that I create this script for my own convenience.
    def __init__(self, file, *args, **kwargs):
        # r = read, wf = write file, wd = write directory
        self.OPERATION = ''
        self.ENCRYPTED = False
        self.FILE = file
        self.IOP_FILENAME = kwargs.get('iop_filename', '')
        self.INCLUDE_DIR = kwargs.get('include_dir', True)
        # Unfortunately, the directories inside .iop are using '/', so os.sep will cause conflict on windows (which uses '\')
        # To make it more convenient, I'll just follow the separator inside of iop/zip instead of standarize it on both sides
        self.EXTRACT_DIR = kwargs.get('dir', '.').replace('\\', '/')
        self.EXTRACT_DIR = self.EXTRACT_DIR + '/' if not self.EXTRACT_DIR.endswith('/') else self.EXTRACT_DIR
        self.BYTESIO = kwargs.get('bytes_io', False)
        self.SILENT = kwargs.get('silent', True)

        self.FILE_LIST = []
        self.RAW_FILE_LIST = []
        self.FILENAME_LIST = {}

        self.RAW_ENTRY = []
        self.ENTRY = []
        self.KEY_ENTRY = {}

        # predefined password from source code https://github.com/LSFDC/.github/tree/main/profile
        self.PASSWORD = kwargs.get('password', 'kr')
        if not self.PASSWORD is None:
            self.PASSWORD = self.PASSWORD.lower()
            self.PW_KR = [b"iosuccess#@", b"XrFrI0%3BF%!0Dcx$30-"]
            self.PW_ID = [b"T*$f40FRjfoe*(fl304d", b"Mfe$%2049eFeodk*&31Z"]
            self.PW_US = [b"eE39DkE!%E0", b"Eg%^io03UT$Cvf921-!$"]
            self.PW_TW = [b"iUT38#@49vnFdjf)(4sg", b"Yi#weT%^903Unv0$2gfj"]
            self.PW_SG = [b"EDgei%^df930%#fj!_=]", b"@7$gjTRreie][!323O++"]
            self.PW_JP = [b"EDgei%^df930%#fj!_=]", b"@7$gjTRreie][!323O++"]
            self.PW_TH = [b"K3$dls49YU#$#eoE3054", b"-_495IUEVJdlsl++32ed"]
            self.PW_CN = [b"-)4TRfkl-41$%dgkrm05", b"|059rtuGReowo@##tkg0"]
            self.PW_LATIN = [b"dus!qhdaksl", b"tkdjqqn!dlfEhrqkfhgo"]
            self.PW_EU = [b"Efedf12-Asv", b"fegG-24qw##4dfe52%3*"]

            if self.PASSWORD == 'kr':
                self.PASSWORD = self.PW_KR
            elif self.PASSWORD == 'id':
                self.PASSWORD = self.PW_ID
            elif self.PASSWORD == 'us':
                self.PASSWORD = self.PW_US
            elif self.PASSWORD == 'tw':
                self.PASSWORD = self.PW_TW
            elif self.PASSWORD == 'sg':
                self.PASSWORD = self.PW_SG
            elif self.PASSWORD == 'jp':
                self.PASSWORD = self.PW_JP
            elif self.PASSWORD == 'th':
                self.PASSWORD = self.PW_TH
            elif self.PASSWORD == 'cn':
                self.PASSWORD = self.PW_CN
            elif self.PASSWORD == 'latin':
                self.PASSWORD = self.PW_LATIN
            elif self.PASSWORD == 'eu':
                self.PASSWORD = self.PW_EU
            else:
                raise KeyError('Unknown password')

        self.__detect_operation()

        if self.OPERATION == 'r':
            self.__process_split()
            self.EXTRACT_ITER = iter(self.ENTRY)
        else:
            self.ENCRYPTED = False if self.PASSWORD is None else True
            self.__process_zipping()

    def __detect_operation(self):
        """
        Function to check whichever operation is more appropriate.
        """
        file = pathlib.Path(self.FILE)
        if not file.exists():
            raise FileNotFoundError('File or directory is not found')

        if self.FILE.endswith('iop'):
            self.OPERATION = 'r'
        else:
            if not self.IOP_FILENAME:
                self.IOP_FILENAME = file.stem + '.iop'
            elif not self.IOP_FILENAME.endswith('.iop'):
                self.IOP_FILENAME += '.iop'

            if file.is_file():
                self.OPERATION = 'wf'
            else:
                self.OPERATION = 'wd'
                # needed for consistency and because zip file use forward slash
                self.FILE = self.FILE.replace('\\', '/')

    def __DOSTime(self, time_input: tuple|float|int) -> tuple|datetime:
        """
        https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time

        Function to convert DOS time/date into epoch, or epoch into DOS Time and DOS Date.
        DOS date/time are packed 16 bit value that specify month, day, year, and time.

        Arguments:
            time: class: `tuple`|`float`|`int`\n
                If argument is a `tuple`, it must contain a tuple of `(time, date)` using the dos format.\n
                If argument is a `float` or `int`

        Return:
            `tuple`: tuple containing `int` `(time, date)` using dos time format that was converted from unix timestamp
            `datetime`: datetime class that was converted from dos time format
        """
        if isinstance(time_input, tuple):
            time = time_input[0]
            date = time_input[1]

            seconds = (time & 0b11111) * 2
            minutes = (time >> 5) & 0b111111
            hours = (time >> 11) & 0b11111

            day = date & 0b11111
            month = (date >> 5) & 0b1111
            year = ((date >> 9) & 0b1111111) + 1980

            return datetime(year, month, day, hours, minutes, seconds)
        else:
            dt = datetime.fromtimestamp(time_input)
            time_field = (
                ((dt.hour & 0b11111) << 11) |
                ((dt.minute & 0b111111) << 5) |
                ((dt.second // 2) & 0b11111)
            )
            date_field = (
                ((dt.year - 1980) & 0b1111111) << 9 |
                ((dt.month & 0b1111) << 5) |
                (dt.day & 0b11111)
            )
            return time_field, date_field

    def __get_crc32(self, filename):
        with open(filename, 'rb') as f:
            crc32 = 0
            while chunk := f.read(65536):
                crc32 = zlib.crc32(chunk, crc32)
        return crc32 & 0xFFFFFFFF
    
    def __encrypt_file(self, filename, time: int = 0):
        """
        Open a file, compress them, and encrypt (if self.ENCRYPTED is set to True) them using ZipCrypto Encryption.
        
        Arguments:
            filename: class: `str`
                The location to the file target
            time: class `int`
                The modified time of the file. Only needed for encryption header
        
        Return:
            tuple: Tuple containing (file_bytes, uncompressed_size)
        """
        with open(filename, 'rb') as f:
            file_bytes = f.read()
            uncompressed_size = len(file_bytes)
            # Python 3.11>
            file_bytes = zlib.compress(file_bytes, wbits=-zlib.MAX_WBITS)
            if self.ENCRYPTED:
                header = bytearray(os.urandom(12))
                # header[10] = (time >> 0) & 0xff
                header[11] = (time >> 8) & 0xff
                encryptor = ZipCrypto(self.PASSWORD[0])
                header = encryptor.encrypt(header)
                file_bytes = encryptor.encrypt(file_bytes)
                file_bytes = header + file_bytes
            return file_bytes, uncompressed_size


    def __process_zipping(self) -> None|io.BytesIO:
        """
        Function that compress file(s), encrypt (if any), and insert them into .iop file. Called upon init
        """
        relative_offset = 0
        iop = io.BytesIO()
        iop.name = self.IOP_FILENAME
        central_bytes = b''
        if self.OPERATION == 'wf':
            # os.path.getctime() would've been much easier, but not cross platform
            # https://stackoverflow.com/questions/237079/how-do-i-get-file-creation-and-modification-date-times
            file = pathlib.Path(self.FILE)
            modified_time = file.stat().st_mtime
            time, date = self.__DOSTime(modified_time)
            crc32 = self.__get_crc32(self.FILE)

            file_bytes, uncompressed_size = self.__encrypt_file(self.FILE, time)

            central_offset = 30 + len(file.name) + len(file_bytes)
            central_offset += 16 if self.ENCRYPTED else 0
            entry = IOP(file_bytes, file.name, self.ENCRYPTED, mod_time=time, mod_date=date, crc32=crc32,
                        uncompressed_size=uncompressed_size, is_last=True, central_offset=central_offset, central_count=1,
                        relative_offset=0)

            iop.write(struct.pack('<IHHHHHIIIHH', *entry.HEADERS['local']))
            iop.write(file.name.encode('utf-8'))
            iop.write(file_bytes)
            if self.ENCRYPTED:
                iop.write(struct.pack('<IIII', *entry.HEADERS['descriptor']))
            iop.write(struct.pack('<IHHHHHHIIIHHHHHII', *entry.HEADERS['cdfh']))
            iop.write(file.name.encode('utf-8'))
            iop.write(struct.pack('<IHHHHIIH', *entry.HEADERS['eocd']))

        else:
            file_list = []
            root_files = []
            # double check, redundant since self.FILE is already ended with '/'
            path = self.FILE if self.FILE.endswith('/') else self.FILE + '/'
            for root, dirs, files in os.walk(path):
                root = root.replace('\\', '/')
                root = root.replace(f'{self.FILE}/', '', 1)
                root = root if root.endswith('/') or root == '' else root + '/'
                if root:
                    file_list.append(root)

                for x in files:
                    # Suggestion: use posixpath which always use '/'
                    file_list.append(os.path.join(root, x).replace('\\', '/'))

            # file_list.sort()
            central_count = len(file_list)
            central_offset = 0
            last_item_check = len(file_list) - 1

            for index, filename in enumerate(file_list):
                is_last = index == last_item_check
                file_path = path + filename
                file = pathlib.Path(file_path)

                is_dir = file.is_dir()
                modified_time = file.stat().st_mtime
                time, date = self.__DOSTime(modified_time)
                if is_dir:
                    file_bytes = None
                    uncompressed_size = 0
                else:
                    file_bytes, uncompressed_size = self.__encrypt_file(file_path, time)

                central_offset += 30
                central_offset += len(filename)
                central_offset += len(file_bytes) if file_bytes else 0
                central_offset += 16 if self.ENCRYPTED and not is_dir else 0

                crc32 = self.__get_crc32(file_path) if not is_dir else 0
                entry = IOP(file_bytes, filename=filename, encrypted=self.ENCRYPTED, mod_time=time,
                            mod_date=date, crc32=crc32, uncompressed_size=uncompressed_size, is_last=is_last,
                            central_offset=central_offset, central_count=central_count,
                            relative_offset=relative_offset)

                local_header = struct.pack('<IHHHHHIIIHH', *entry.HEADERS['local'])
                filename_header = filename.encode('utf-8')
                iop.write(local_header)
                iop.write(filename_header)
                iop.write(file_bytes if file_bytes else b'')
                relative_offset += len(local_header)
                relative_offset += len(filename_header)
                relative_offset += len(file_bytes) if file_bytes else 0
                if self.ENCRYPTED and not is_dir:
                    descriptor_header = struct.pack('<IIII', *entry.HEADERS['descriptor'])
                    iop.write(descriptor_header)
                    relative_offset += len(descriptor_header)
                central_header = struct.pack('<IHHHHHHIIIHHHHHII', *entry.HEADERS['cdfh'])
                central_bytes += central_header
                central_bytes += filename_header
                if is_last:
                    entry.HEADERS['eocd'][5] = len(central_bytes)
                    end_header = struct.pack('<IHHHHIIH', *entry.HEADERS['eocd'])
                    iop.write(central_bytes)
                    iop.write(end_header)

                if not self.SILENT:
                    if is_dir:
                        print('Directory written: ', filename)
                    else:
                        print('File written: ', filename)

        if self.BYTESIO:
            return iop
        else:
            pathlib.Path(iop.name).write_bytes(iop.getbuffer())
            iop.close()
            if not self.SILENT:
                print('File saved: ', self.IOP_FILENAME)

    def __process_split(self):
        """
        Split each local header, file entry, and central into a list and then set the self.ENTRY variable. Called upon init
        """
        with open(self.FILE, 'rb') as f:
            data = f.read()
            
        # Double check, kind of redundant
        sig = struct.unpack('<I', data[:4])
        if not sig[0] == int.from_bytes(ZIP_LOCAL_HEADER_SIGNATURE, byteorder='little'):
            raise ValueError('Not an iop file')

        # I don't understand regex split, so I'll just scrape this
        # I wanted for it to return each entry with its delimiter, but regex just splits it for each delimiter and the match.
        # [(...), (delimiter), (group), (delimiter), (group), ...] which I don't know how to process
        # Catching them on wildcard doesn't seemed to work either, it will instead capture everything (rb'(pk\x03\x04.*)')
        # self.RAW_ENTRY = re.split(ZIP_LOCAL_HEADER_SIGNATURE, data)
        #
        # Here's how I'd want my entries looked like
        # [ [local header, file entry, descriptor (if any), central], [local, file, ...] [..., eocd (only for last entry)] ]
        # But of course, the challenge is to pair the local, file, and central altogether, it probably not that hard
        # since they always have the same order.
        # This is much convenient since the central can be accessed from each file entry, as opposed to having the entire central
        # headers on the last entry
        end_header = data.split(ZIP_END_CENTRAL_HEADER_SIGNATURE)
        central_entries = end_header[0].split(ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE, 1)
        end_header = ZIP_END_CENTRAL_HEADER_SIGNATURE + end_header[-1]
        file_entries = [ZIP_LOCAL_HEADER_SIGNATURE + _ for _ in central_entries[0].split(ZIP_LOCAL_HEADER_SIGNATURE) if _]
        central_entries = ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE + central_entries[-1]
        central_entries = [ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE + _ for _ in central_entries.split(ZIP_CENTRAL_DIRECTORY_HEADER_SIGNATURE) if _]

        if len(file_entries) != len(central_entries):
            # Maybe the archive is corrupted? Because each file entry are supposed to have their own central
            raise RuntimeError('File entry or Central Headers contains more than one another. The file might be corrupted.')

        for i, (local, central) in enumerate(zip(file_entries, central_entries)):
            if not i == len(file_entries) - 1:
                self.RAW_ENTRY.append([local, central])
            else:
                self.RAW_ENTRY.append([local, central, end_header])

        last_item_check = len(self.RAW_ENTRY) - 1
        self.ENTRY = [IOP(_, is_last=(i==last_item_check)) for i, _ in enumerate(self.RAW_ENTRY)]

        # self.RAW_ENTRY = data.split(ZIP_LOCAL_HEADER_SIGNATURE)
        # self.RAW_ENTRY = [ZIP_LOCAL_HEADER_SIGNATURE + _ for _ in self.RAW_ENTRY if _]

    def __file_list(self):
        """
        Append all files into a variable. ~~Provide two variables, one excluding dir, and one is for indexing purpose.~~
        """
        self.FILE_LIST = [_.FILENAME for _ in self.ENTRY if not _.IS_DIR]
        # self.RAW_FILE_LIST = [_.FILENAME for _ in self.ENTRY]
        self.KEY_ENTRY = {k.FILENAME:v for k, v in zip(self.ENTRY, self.ENTRY)}
        return

    # Was meant for extract_by_name() function, but was later scraped
    # def __filename_list(self) -> None:
    #     """
    #     Append all filename and their respective filename path into a dictionary variable.
    #     The base filename will be set as key, while the full path will be set as value.

    #     If there were duplicates, the value would be set as list instead of str
    #     """
    #     if not self.FILE_LIST:
    #         self.__file_list()

    #     tmp = collections.defaultdict(list)

    #     for x in self.FILE_LIST:
    #         filename = os.path.basename(x)
    #         tmp[filename].append(x)

    #     self.FILENAME_LIST = {
    #         filename: paths if len(paths) > 1 else paths[0]
    #         for filename, paths in tmp.items()
    #     }
    #     return

    def __decrypt_bytes(self, entry: IOP) -> bytes:
        """
        Decrypt a bytes using specified password. Raise an error if both password is incorrect.

        Arguments:
            entry: class: `iop`\n
                IOP class

        Return:
            bytes: The decrypted bytes content
        """
        if not self.PASSWORD:
            raise ValueError('File is encrypted, password is not set')

        password = self.PASSWORD[0]
        while True:
            decryptor = ZipCrypto(pwd=password)
            check = decryptor.decrypt(entry.ENTRY_BYTES[:12])
            crc_check = (entry.MOD_TIME >> 8) & 0xff
            if check[11] != crc_check:
                if password != self.PASSWORD[1]:
                    password = self.PASSWORD[1]
                    continue
                else:
                    raise RuntimeError('Password incorrect')
            break

        return decryptor.decrypt(entry.ENTRY_BYTES[12:])

    def __decompress_bytes(self, entry: bytes) -> bytes:
        """
        Decompress a bytes

        Arguments:
            entry: class: `bytes`\n
                Bytes containing the compressed content

        Return:
            bytes: The uncompressed bytes content
        """
        return zlib.decompress(entry, wbits=-zlib.MAX_WBITS)

    def __extract(self, filename: str, file: bytes) -> None|io.BytesIO:
        """
        Function to save decompressed bytes into file or return them as BytesIO.

        Arguments:
            filename: class: `str`\n
                The specified filename and its path (if any)
            file: class: `bytes`\n
                Bytes containing the uncompressed content

        Return:
            None: file is saved
            BytesIO: if `bytes_io` parameters is set to `True`, returns this instead of `None`
        """
        if self.BYTESIO:
            file_bytesio = io.BytesIO(file)
            file_bytesio.name = filename
            return file_bytesio
        else:
            path = self.EXTRACT_DIR + (filename if self.INCLUDE_DIR else os.path.basename(filename))
            directory = os.path.dirname(path)
            if not os.path.exists(directory):
                os.makedirs(directory)
            # Appearantly it threw an error if directory does not exist, even though it was a `write if not exist` operation
            with open(path, 'wb+') as f:
                f.write(file)

            if not self.SILENT:
                print('Extracted file: ', filename)
        return

    def list_file(self) -> list[str]:
        """
        Returns a list of string containing all the filenames and their directories

        Return:
            list[str]: list containing each filenames and their directories
        """
        if not self.FILE_LIST:
            self.__file_list()
        return self.FILE_LIST

    def __process_entry(self, entry: IOP) -> None|bool|io.BytesIO:
        """
        Function to process entry.

        Return:
            None: file is saved
            False: entry is a directory
            BytesIO: if `bytes_io` parameters is set to `True`, returns this instead of `None`
        """
        if entry.IS_DIR:
            return False

        entry_bytes = entry.ENTRY_BYTES
        if entry.ENCRYPTED:
            entry_bytes = self.__decrypt_bytes(entry)

        entry_bytes = self.__decompress_bytes(entry_bytes)

        return self.__extract(entry.FILENAME, entry_bytes)

    def extract(self) -> None|bool|io.BytesIO:
        """
        Extract the first item, or iter to the next one

        Return:
            None: operation completed and is saved
            False: no files to extract
            BytesIO: if `bytes_io` parameters is set to `True`, returns this instead of `None`
        """
        if not self.OPERATION == 'r':
            raise ValueError("Unsupported operation, expected 'r' (read)")

        try:
            while True:
                entry = next(self.EXTRACT_ITER)
                file = self.__process_entry(entry)
                if file is False:
                    continue
                return file
        except StopIteration:
            print('Nothing to extract')
            return False

    def extract_by_name(self, filename) -> None|bool|io.BytesIO|dict:
        """
        Extract by their filename.

        Parameters:
            filename: class: `str`\n
                The specified filename inside .iop

        Return:
            None: file exist and is saved
            False: file not found
            BytesIO: if `bytes_io` parameter is set to `True` and file is found, returns this instead of `None`
            dict: same as BytesIO, if it result more than one file. The dict contains {filename: io.BytesIO or [io.BytesIO, ..]}
        """
        if not self.OPERATION == 'r':
            raise ValueError("Unsupported operation, expected 'r' (read)")

        if not self.KEY_ENTRY:
            self.__file_list()

        entry = self.KEY_ENTRY.get(filename, None)
        if not entry:
            return False

        file = self.__process_entry(entry)
        return file

    def extract_all(self) -> None|dict:
        """
        Extract all contents inside the .iop file

        Return:
            None: operation completed and is saved
            dict: if `bytes_io` parameter is set to `True`, returns this instead of `None`. The dict contains {filename: io.BytesIO or [io.BytesIO, ..]}
        """
        if not self.OPERATION == 'r':
            raise ValueError("Unsupported operation, expected 'r' (read)")

        files = {}
        for entry in self.ENTRY:
            file = self.__process_entry(entry)
            if file is False:
                continue
            if file:
                files[file.name] = file
        return files if files else None