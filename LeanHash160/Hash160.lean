import LeanHash160.SHA256
import LeanHash160.RIPEMD160

namespace LeanHash160

/-- Bitcoin HASH160: RIPEMD-160 applied to the SHA-256 digest. -/
def hash160 (bytes : ByteArray) : ByteArray :=
  RIPEMD160.hash (SHA256.hash bytes)

end LeanHash160
