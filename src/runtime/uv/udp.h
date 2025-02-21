/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/net_addr.h"
#include "runtime/object_ref.h"

namespace lean {

static lean_external_class * g_uv_udp_socket_external_class = NULL;
void initialize_libuv_udp_socket();

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

// Structure for managing a single UDP socket object, including promise handling,
// connection state, and read/write buffers.
typedef struct {
    uv_udp_t *      m_uv_udp;           // LibUV UDP handle.
    lean_object *   m_promise_read;     // The associated promise for asynchronous results for reading from the socket.
    lean_object *   m_byte_array;       // The data stored.
    uint64_t        m_buffer_size;      // The size of the thing that is going to be stored
} lean_uv_udp_socket_object;

// =======================================
// UDP socket object manipulation functions.
static inline lean_object* lean_uv_udp_socket_new(lean_uv_udp_socket_object * s) { return lean_alloc_external(g_uv_udp_socket_external_class, s); }
static inline lean_uv_udp_socket_object* lean_to_uv_udp_socket(lean_object * o) { return (lean_uv_udp_socket_object*)(lean_get_external_data(o)); }

#endif

// =======================================
// UDP Socket Operations
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_new();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_bind(b_obj_arg socket, b_obj_arg addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_connect(b_obj_arg socket, b_obj_arg addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_send(b_obj_arg socket, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_recv(b_obj_arg socket, uint64_t buffer_size);

// =======================================
// UDP Socket Utility Functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getpeername(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getsockname(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_broadcast(b_obj_arg socket, int32_t enable);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_loop(b_obj_arg socket, int32_t enable);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_ttl(b_obj_arg socket, uint32_t ttl);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_membership(b_obj_arg socket, b_obj_arg multicast_addr, b_obj_arg interface_addr, int32_t membership);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_interface(b_obj_arg socket, b_obj_arg interface_addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_ttl(b_obj_arg socket, uint32_t ttl);

}
