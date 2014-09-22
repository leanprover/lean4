/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <vector>
#include "util/thread.h"
#include "util/debug.h"
namespace lean {
/**
   \brief Template for creating objects that can be attached to "extensions".
*/
template<typename T>
class extensible_object : public T {
public:
    class extension {
        friend class extensible_object;
        extensible_object * m_owner;
    public:
        extension():m_owner(nullptr) {}
        virtual ~extension() {}
        extensible_object & get_owner() { return *m_owner; }
    };
private:
    std::vector<std::unique_ptr<extension>> m_extensions;
public:
    template<typename... Args>
    extensible_object(Args &&... args):T(std::forward<Args>(args)...) {}

    typedef std::unique_ptr<extension> (*mk_extension)();

    class extension_factory {
        std::vector<mk_extension> m_makers;
        mutex                     m_makers_mutex;
    public:
        unsigned register_extension(mk_extension mk) {
            lock_guard<mutex> lock(m_makers_mutex);
            unsigned r = m_makers.size();
            m_makers.push_back(mk);
            return r;
        }

        std::unique_ptr<extension> mk(unsigned extid) {
            lock_guard<mutex> lock(m_makers_mutex);
            return m_makers[extid]();
        }
    };

    static extension_factory * g_extension_factory;
    static void initialize() { g_extension_factory = new extension_factory(); }
    static void finalize() { delete g_extension_factory; }
    static extension_factory & get_extension_factory() { return *g_extension_factory; }

    static unsigned register_extension(mk_extension mk) {
        return get_extension_factory().register_extension(mk);
    }

    extension & get_extension_core(unsigned extid) {
        if (extid >= m_extensions.size())
            m_extensions.resize(extid+1);
        if (!m_extensions[extid]) {
            std::unique_ptr<extension> ext = get_extension_factory().mk(extid);
            ext->m_owner = this;
            m_extensions[extid].swap(ext);
        }
        return *(m_extensions[extid].get());
    }

    template<typename Ext> Ext & get_extension(unsigned extid) {
        extension & ext = get_extension_core(extid);
        lean_assert(dynamic_cast<Ext*>(&ext) != nullptr);
        return static_cast<Ext&>(ext);
    }
};
template<typename T>
typename extensible_object<T>::extension_factory *
extensible_object<T>::g_extension_factory = nullptr;
}
