/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>

namespace lean {

extern "C" void initialize_libidn2();

// =======================================
// LibIDN2 Punycode functions.
extern "C" LEAN_EXPORT lean_obj_res lean_idn2_to_punycode(lean_obj_arg);

}