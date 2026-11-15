"""Small regression tests for the offline verifier; does not require the 10 GB evidence."""
import hashlib
import tempfile
import unittest
import zipfile
from pathlib import Path

from verify_release import VerificationError, digest_member, require, sha256_path

class VerifierUnitTests(unittest.TestCase):
    def test_hash_streaming(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "example.bin"
            p.write_bytes(b"hello" * 1000)
            self.assertEqual(sha256_path(p), hashlib.sha256(p.read_bytes()).hexdigest())

    def test_member_hash_and_size(self):
        content = b"proof artifact" * 50
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "test.zip"
            with zipfile.ZipFile(p, "w", zipfile.ZIP_DEFLATED) as z:
                z.writestr("objects/demo.olean", content)
            with zipfile.ZipFile(p) as z:
                self.assertEqual(digest_member(z,"objects/demo.olean",len(content),hashlib.sha256(content).hexdigest()),len(content))
                with self.assertRaises(VerificationError):
                    digest_member(z,"objects/demo.olean",len(content)+1,hashlib.sha256(content).hexdigest())
                with self.assertRaises(VerificationError):
                    digest_member(z,"objects/demo.olean",len(content),"0"*64)

    def test_require_cannot_be_optimized_away(self):
        with self.assertRaises(VerificationError):
            require(False,"required condition failed")

if __name__ == "__main__":
    unittest.main()
