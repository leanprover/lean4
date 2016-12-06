/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include "kernel/environment.h"
#include "kernel/expr.h"

namespace lean  {
    static const char * LEAN_OBJ_TYPE = "lean::vm_obj";
    // static const char * LEAN_ERR = "lean::runtime_error";

    class cpp_emitter {
        int m_width;
    public:
        std::fstream * m_output_stream;

        cpp_emitter(std::string path) : m_width(0), m_output_stream(nullptr) {
            this->m_output_stream =
                new std::fstream(path.c_str(), std::ios_base::out);
        }

        ~cpp_emitter() {
            this->m_output_stream->flush();
            this->m_output_stream->close();
            delete this->m_output_stream;
        }

        void emit_headers();
        void indent();
        void unindent();

        void emit_name(name const & n) {
            this->emit_string("name({\"");
            this->emit_string(n.to_string("\"}, {\"").c_str());
            this->emit_string("\"})");
        }

        void emit_prototype(name const & n, unsigned arity);
        void emit_indented(const char * str);
        void emit_string(const char * str);
        void emit_indented_line(const char * str);
        void mangle_name(name const & n);
        void emit_declare_vm_builtin(name const & n);
    };
}
