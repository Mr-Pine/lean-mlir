import unittest
from extract_byte_globals import extract, decode_string


def op(value='"\\01\\FFab"', ty='array<4 x i8>', constant='constant, ', alignment=8):
    return ('"llvm.mlir.global"() <{addr_space = 0 : i32, '
            f'alignment = {alignment} : i64, {constant}global_type = !llvm.{ty}, '
            f'sym_name = "table", value = {value}' + '}> ({\n}) : () -> ()\n')


class Globals(unittest.TestCase):
    def test_string(self):
        self.assertEqual(extract(op(), ['table'])[0]['bytes_hex'], '01ff6162')
        self.assertEqual(decode_string(r'\00\7F\80\FF'), bytes([0, 127, 128, 255]))

    def test_dense(self):
        self.assertEqual(extract(op('dense<0> : tensor<4xi8>'), ['table'])[0]['bytes_hex'], '00000000')
        self.assertEqual(extract(op('dense<-1> : tensor<4xi8>'), ['table'])[0]['bytes_hex'], 'ffffffff')

    def test_reject_unsafe(self):
        bad = [op(constant=''), op(ty='ptr'), op(alignment=3), op('"x"'),
               op('dense<256> : tensor<4xi8>'), op('dense<0> : tensor<3xi8>'),
               op().replace('addr_space = 0', 'addr_space = 1'),
               op().replace('}) :', '  %0 = "llvm.mlir.addressof"()\n}) :'),
               op('"\\ZZ"')]
        for text in bad:
            with self.subTest(text=text), self.assertRaises(ValueError):
                extract(text, ['table'])

    def test_missing_duplicate(self):
        for text, names in [('', ['table']), (op() + op(), ['table']), (op(), ['table', 'table'])]:
            with self.assertRaises(ValueError):
                extract(text, names)


if __name__ == '__main__':
    unittest.main()
