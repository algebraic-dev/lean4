/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.System

namespace Std
namespace Internal

/--
Convert a Unicode string to punycode (ASCII-compatible encoding).
Returns `none` if the conversion fails.
-/
@[extern "lean_idn2_to_punycode"]
opaque idn2ToPunycodeFn : String → Option String

end Internal
end Std
