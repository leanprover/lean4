/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
*/
#include <string>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <iomanip>
#include <lean/lean.h>
#include "runtime/object.h"

namespace lean {

static std::string dot_escape(std::string const & s) {
    std::string result;
    result.reserve(s.size());
    for (char c : s) {
        switch (c) {
        case '"':  result += "\\\""; break;
        case '\\': result += "\\\\"; break;
        case '<':  result += "\\<"; break;
        case '>':  result += "\\>"; break;
        case '{':  result += "\\{"; break;
        case '}':  result += "\\}"; break;
        case '|':  result += "\\|"; break;
        case '\n': result += "\\n"; break;
        case '\r': result += "\\r"; break;
        case '\t': result += "\\t"; break;
        default:
            if (static_cast<unsigned char>(c) < 0x20) {
                char buf[8];
                snprintf(buf, sizeof(buf), "\\x%02x", static_cast<unsigned char>(c));
                result += buf;
            } else {
                result += c;
            }
        }
    }
    return result;
}

static std::string hex_dump(uint8_t const * data, size_t len) {
    std::ostringstream oss;
    oss << "0x";
    for (size_t i = 0; i < len; i++) {
        oss << std::hex << std::setfill('0') << std::setw(2) << static_cast<unsigned>(data[i]);
    }
    return oss.str();
}

static std::string node_id(lean_object * o) {
    std::ostringstream oss;
    oss << "obj_" << std::hex << reinterpret_cast<uintptr_t>(o);
    return oss.str();
}

static std::string addr_str(lean_object * o) {
    std::ostringstream oss;
    oss << "0x" << std::hex << reinterpret_cast<uintptr_t>(o);
    return oss.str();
}

static std::string rc_str(lean_object * o) {
    int rc = o->m_rc;
    if (rc == 0) return "persistent";
    if (rc < 0) return "mt(" + std::to_string(std::abs(rc)) + ")";
    return std::to_string(rc);
}

struct object_graph_builder {
    std::ostringstream m_out;
    std::unordered_set<lean_object*> m_visited;
    std::vector<lean_object*> m_worklist;

    struct edge {
        std::string from_node;
        std::string from_port;
        std::string to_node;
    };
    std::vector<edge> m_edges;

    void add_edge(lean_object * parent, std::string const & port, lean_object * child) {
        m_edges.push_back({node_id(parent), port, node_id(child)});
        if (m_visited.find(child) == m_visited.end()) {
            m_visited.insert(child);
            m_worklist.push_back(child);
        }
    }

    std::string field_cell(lean_object * parent, std::string const & name, lean_object * val) {
        if (lean_is_scalar(val)) {
            return name + ": box(" + std::to_string(lean_unbox(val)) + ")";
        } else {
            add_edge(parent, name, val);
            return "<" + name + "> " + name;
        }
    }

    void emit_ctor(lean_object * o) {
        unsigned tag = lean_ptr_tag(o);
        unsigned num_objs = lean_ctor_num_objs(o);
        size_t byte_size = lean_object_byte_size(o);
        size_t scalar_offset = sizeof(lean_ctor_object) + num_objs * sizeof(lean_object*);
        size_t scalar_size = byte_size > scalar_offset ? byte_size - scalar_offset : 0;

        std::string header = "Ctor(" + std::to_string(tag) + ") @ " + addr_str(o) + " | rc=" + rc_str(o);

        std::vector<std::string> fields;
        for (unsigned i = 0; i < num_objs; i++) {
            lean_object * child = lean_ctor_get(o, i);
            fields.push_back(field_cell(o, "f" + std::to_string(i), child));
        }
        if (scalar_size > 0) {
            uint8_t * sdata = lean_ctor_scalar_cptr(o);
            fields.push_back("scalar: " + dot_escape(hex_dump(sdata, scalar_size)));
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "}";
        if (!fields.empty()) {
            m_out << " | {";
            for (size_t i = 0; i < fields.size(); i++) {
                if (i > 0) m_out << " | ";
                m_out << fields[i];
            }
            m_out << "}";
        }
        m_out << "\"];\n";
    }

    void emit_closure(lean_object * o) {
        unsigned arity = lean_closure_arity(o);
        unsigned num_fixed = lean_closure_num_fixed(o);
        void * fun = lean_closure_fun(o);
        std::ostringstream fun_oss;
        fun_oss << "0x" << std::hex << reinterpret_cast<uintptr_t>(fun);

        std::string header = "Closure @ " + addr_str(o) + " | rc=" + rc_str(o)
            + " | arity=" + std::to_string(arity) + " | fun=" + fun_oss.str();

        std::vector<std::string> fields;
        for (unsigned i = 0; i < num_fixed; i++) {
            lean_object * child = lean_closure_get(o, i);
            fields.push_back(field_cell(o, "a" + std::to_string(i), child));
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "}";
        if (!fields.empty()) {
            m_out << " | {";
            for (size_t i = 0; i < fields.size(); i++) {
                if (i > 0) m_out << " | ";
                m_out << fields[i];
            }
            m_out << "}";
        }
        m_out << "\"];\n";
    }

    void emit_array(lean_object * o) {
        size_t sz = lean_array_size(o);

        std::string header = "Array @ " + addr_str(o) + " | rc=" + rc_str(o)
            + " | size=" + std::to_string(sz);

        std::vector<std::string> fields;
        for (size_t i = 0; i < sz; i++) {
            lean_object * elem = lean_array_get_core(o, i);
            fields.push_back(field_cell(o, "e" + std::to_string(i), elem));
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "}";
        if (!fields.empty()) {
            m_out << " | {";
            for (size_t i = 0; i < fields.size(); i++) {
                if (i > 0) m_out << " | ";
                m_out << fields[i];
            }
            m_out << "}";
        }
        m_out << "\"];\n";
    }

    void emit_sarray(lean_object * o) {
        size_t sz = lean_sarray_size(o);
        unsigned elem_size = lean_sarray_elem_size(o);

        std::string header = "ScalarArray @ " + addr_str(o) + " | rc=" + rc_str(o)
            + " | size=" + std::to_string(sz) + " | elem_size=" + std::to_string(elem_size);

        std::vector<std::string> fields;
        if (elem_size == 1) {
            for (size_t i = 0; i < sz; i++) {
                uint8_t elem = lean_byte_array_uget(o, i);
                fields.push_back("e" + std::to_string(i) + ": " + std::to_string(elem));
            }
        } else if (elem_size == 8) {
            for (size_t i = 0; i < sz; i++) {
                double elem = lean_float_array_uget(o, i);
                fields.push_back("e" + std::to_string(i) + ": " + std::to_string(elem));
            }
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "}";
        if (!fields.empty()) {
            m_out << " | {";
            for (size_t i = 0; i < fields.size(); i++) {
                if (i > 0) m_out << " | ";
                m_out << fields[i];
            }
            m_out << "}";
        }
        m_out << "\"];\n";
    }

    void emit_string(lean_object * o) {
        size_t len = lean_string_len(o);
        char const * cstr = lean_string_cstr(o);
        std::string content(cstr);
        if (content.size() > 48) {
            content = content.substr(0, 48) + "...";
        }

        std::string header = "String @ " + addr_str(o) + " | rc=" + rc_str(o)
            + " | len=" + std::to_string(len);

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "} | {"
              << dot_escape(content) << "}\"];\n";
    }

    void emit_mpz(lean_object * o) {
        std::string val = mpz_value(o).to_string();
        std::string label = "MPZ @ " + addr_str(o) + " | rc=" + rc_str(o) + " | " + val;
        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(label) << "}\"];\n";
    }

    void emit_thunk(lean_object * o) {
        lean_thunk_object * t = lean_to_thunk(o);
        lean_object * val = t->m_value.load(std::memory_order_seq_cst);
        lean_object * cls = t->m_closure.load(std::memory_order_seq_cst);

        std::string header = "Thunk @ " + addr_str(o) + " | rc=" + rc_str(o);

        std::vector<std::string> fields;
        if (val != nullptr && !lean_is_scalar(val)) {
            add_edge(o, "value", val);
            fields.push_back("<value> value");
        } else if (val != nullptr) {
            fields.push_back("value: " + std::to_string(lean_unbox(val)));
        } else {
            fields.push_back("value: null");
        }
        if (cls != nullptr && !lean_is_scalar(cls)) {
            add_edge(o, "closure", cls);
            fields.push_back("<closure> closure");
        } else if (cls != nullptr) {
            fields.push_back("closure: " + std::to_string(lean_unbox(cls)));
        } else {
            fields.push_back("closure: null");
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "} | {";
        for (size_t i = 0; i < fields.size(); i++) {
            if (i > 0) m_out << " | ";
            m_out << fields[i];
        }
        m_out << "}\"];\n";
    }

    void emit_task(lean_object * o) {
        lean_task_object * t = lean_to_task(o);
        lean_object * val = t->m_value.load(std::memory_order_seq_cst);

        std::string header = "Task @ " + addr_str(o) + " | rc=" + rc_str(o);

        std::string field;
        if (val != nullptr && !lean_is_scalar(val)) {
            add_edge(o, "value", val);
            field = "<value> value";
        } else if (val != nullptr) {
            field = "value: " + std::to_string(lean_unbox(val));
        } else {
            field = "value: null";
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "} | {" << field << "}\"];\n";
    }

    void emit_ref(lean_object * o) {
        lean_ref_object * r = lean_to_ref(o);
        lean_object * val = r->m_value;

        std::string header = "Ref @ " + addr_str(o) + " | rc=" + rc_str(o);

        std::string field;
        if (val != nullptr && !lean_is_scalar(val)) {
            add_edge(o, "value", val);
            field = "<value> value";
        } else if (val != nullptr) {
            field = "value: box(" + std::to_string(lean_unbox(val)) + ")";
        } else {
            field = "value: null";
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "} | {" << field << "}\"];\n";
    }

    void emit_external(lean_object * o) {
        lean_external_object * e = lean_to_external(o);
        std::ostringstream data_oss;
        data_oss << "0x" << std::hex << reinterpret_cast<uintptr_t>(e->m_data);
        std::string label = "External @ " + addr_str(o) + " | rc=" + rc_str(o) + " | data=" + data_oss.str();
        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(label) << "}\"];\n";
    }

    void emit_promise(lean_object * o) {
        lean_promise_object * p = lean_to_promise(o);
        lean_task_object * result = p->m_result;

        std::string header = "Promise @ " + addr_str(o) + " | rc=" + rc_str(o);

        std::string field;
        if (result != nullptr) {
            add_edge(o, "result", reinterpret_cast<lean_object*>(result));
            field = "<result> result";
        } else {
            field = "result: null";
        }

        m_out << "  " << node_id(o) << " [label=\"{" << dot_escape(header) << "} | {" << field << "}\"];\n";
    }

    void emit_node(lean_object * o) {
        uint8_t tag = lean_ptr_tag(o);
        if (tag <= LeanMaxCtorTag) {
            emit_ctor(o);
        } else {
            switch (tag) {
            case LeanClosure:     emit_closure(o);  break;
            case LeanArray:       emit_array(o);   break;
            case LeanScalarArray: emit_sarray(o);  break;
            case LeanString:      emit_string(o);   break;
            case LeanMPZ:         emit_mpz(o);      break;
            case LeanThunk:       emit_thunk(o);    break;
            case LeanTask:        emit_task(o);     break;
            case LeanRef:         emit_ref(o);      break;
            case LeanExternal:    emit_external(o); break;
            case LeanPromise:     emit_promise(o);  break;
            default:
                m_out << "  " << node_id(o) << " [label=\"Unknown(tag=" << std::to_string(tag)
                      << ") @ " << addr_str(o) << "\"];\n";
                break;
            }
        }
    }

    std::string build(lean_object * root) {
        m_out << "digraph lean_object_graph {\n";
        m_out << "  rankdir=LR;\n";
        m_out << "  node [shape=record, fontname=\"Courier\"];\n";

        if (root == nullptr) {
            m_out << "}\n";
            return m_out.str();
        }

        if (lean_is_scalar(root)) {
            m_out << "  scalar_root [label=\"Scalar: " << lean_unbox(root) << "\"];\n";
            m_out << "}\n";
            return m_out.str();
        }

        m_visited.insert(root);
        m_worklist.push_back(root);

        while (!m_worklist.empty()) {
            lean_object * o = m_worklist.back();
            m_worklist.pop_back();
            emit_node(o);
        }

        for (auto const & e : m_edges) {
            m_out << "  " << e.from_node << ":" << e.from_port << " -> " << e.to_node << ":n" << ";\n";
        }

        m_out << "}\n";
        return m_out.str();
    }
};

extern "C" LEAN_EXPORT lean_obj_res lean_object_graph_to_dot(b_lean_obj_arg root) {
    object_graph_builder builder;
    std::string dot = builder.build(root);
    return mk_string(dot);
}

} // namespace lean
