#include "runtime/idn2.h"

#ifndef LEAN_EMSCRIPTEN
#include <idn2.h>
#include <string.h>
#include <stdlib.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

extern "C" void initialize_libidn2();

/* Lean.idn2ToPunycodeFn : String → Option String */
extern "C" LEAN_EXPORT lean_obj_res lean_idn2_to_punycode(lean_obj_arg str) {
    // Extract the input string from Lean object
    const char* input = lean_string_cstr(str);
    char* output = nullptr;

    int rc = idn2_to_ascii_8z(input, &output, IDN2_NONTRANSITIONAL);

    if (rc == IDN2_OK && output != nullptr) {
        // Success: create Lean string and wrap in Some
        lean_obj_res result_str = lean_mk_string(output);
        lean_obj_res some_result = lean_alloc_ctor(1, 1, 0); // Some constructor
        lean_ctor_set(some_result, 0, result_str);

        // Free the output allocated by libidn2
        free(output);

        return some_result;
    } else {
        // Error: return None
        if (output != nullptr) {
            free(output);
        }
        return lean_alloc_ctor(0, 0, 0); // None constructor
    }
}

#else

extern "C" void initialize_libidn2() {}

/* Lean.idn2ToPunycodeFn : String → Option String */
extern "C" LEAN_EXPORT lean_obj_res lean_idn2_to_punycode(lean_obj_arg str) {
    // In Emscripten build, just return None
    return lean_alloc_ctor(0, 0, 0); // None constructor
}

#endif

}