/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/abstract_parser.h"
#include "library/io_state.h"
#include "util/priority_queue.h"

#ifndef LEAN_DEFAULT_PRIORITY
#define LEAN_DEFAULT_PRIORITY 1000u
#endif

namespace lean {

struct attr_data {
    virtual unsigned hash() const {
        return 0;
    }
    virtual void print(std::ostream &) {}
    virtual ~attr_data() {}
};

typedef std::shared_ptr<attr_data> attr_data_ptr;
struct attr_config;

class attribute {
    friend struct attr_config;
    friend class  decl_attributes;
private:
    std::string m_id;
    std::string m_descr;
    std::string m_token;
protected:
    environment set_core(environment const &, io_state const &, name const &, attr_data_ptr, bool) const;

    virtual environment set_untyped(environment const &, io_state const &, name const &, attr_data_ptr, bool) const = 0;
    virtual void write_entry(serializer &, attr_data const &) const = 0;
    virtual attr_data_ptr read_entry(deserializer &) const = 0;
public:
    attribute(char const * id, char const * descr) : m_id(id), m_descr(descr), m_token(std::string("[") + id) {}
    virtual ~attribute() {}

    std::string const & get_name() const { return m_id; }
    std::string const & get_token() const { return m_token; }

    virtual attr_data_ptr get(environment const &, name const &) const;
    virtual void get_instances(environment const &, buffer<name> &) const;
    virtual attr_data_ptr parse_data(abstract_parser &) const;
};

typedef std::shared_ptr<attribute const> attribute_ptr;

/** \brief An attribute without associated data or priority declaration */
class basic_attribute : public attribute {
public:
    typedef std::function<environment(environment const &, io_state const &, name const &, bool)> on_set_proc;
private:
    on_set_proc m_on_set;
protected:
    virtual void write_entry(serializer &, attr_data const &) const override final {}
    virtual attr_data_ptr read_entry(deserializer &) const override final { return attr_data_ptr(new attr_data); }
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, attr_data_ptr,
                                    bool persistent) const override final {
        return set(env, ios, n, persistent);
    }
public:
    basic_attribute(char const * id, char const * descr, on_set_proc on_set) : attribute(id, descr),
                                                                               m_on_set(on_set) {}
    basic_attribute(char const * id, char const * descr) : basic_attribute(id, descr, {}) {}
    virtual environment set(environment const & env, io_state const & ios, name const & n, bool persistent) const;
};

// TODO(sullrich): Let the attribute handle priority parsing itself by introducing a custom
// syntax (something like [attr:prio]?)
class prio_attribute : public attribute {
public:
    typedef std::function<environment(environment const &, io_state const &, name const &, unsigned, bool)> on_set_proc;
private:
    on_set_proc m_on_set;
protected:
    virtual void write_entry(serializer &, attr_data const &) const override final {}
    virtual attr_data_ptr read_entry(deserializer &) const override final { return attr_data_ptr(new attr_data); }
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, attr_data_ptr data,
                                    bool persistent) const override final {
        // TODO(sullrich): Use priority from `data` as soon as available
        lean_unreachable();
    }
public:
    prio_attribute(char const * id, char const * descr, on_set_proc on_set) : attribute(id, descr),
                                                                              m_on_set(on_set) {}
    prio_attribute(char const * id, char const * descr) : prio_attribute(id, descr, {}) {}
    virtual environment set(environment const & env, io_state const & ios, name const & n, unsigned prio,
                            bool persistent) const;
};

template<typename Data>
class typed_attribute : public attribute {
public:
    typedef std::function<environment(environment const &, io_state const &, name const &, Data const &, bool)>
            on_set_proc;
private:
    on_set_proc m_on_set;
protected:
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, attr_data_ptr data,
                                    bool persistent) const override final {
        lean_assert(dynamic_cast<Data const *>(&*data));
        return set(env, ios, n, static_cast<Data const &>(*data), persistent);
    }

    virtual void write_entry(serializer & s, attr_data const & data) const final override {
        lean_assert(dynamic_cast<Data const *>(&data));
        static_cast<Data const &>(data).write(s);
    }
    virtual attr_data_ptr read_entry(deserializer & d) const final override {
        auto data = new Data;
        data->read(d);
        return attr_data_ptr(data);
    }
public:
    typed_attribute(char const * id, char const * descr, on_set_proc on_set) : attribute(id, descr),
                                                                               m_on_set(on_set) {}
    typed_attribute(char const * id, char const * descr) : typed_attribute(id, descr, {}) {}
    virtual environment set(environment const & env, io_state const & ios, name const & n, Data const & data, bool persistent) const {
        auto env2 = set_core(env, ios, n, std::unique_ptr<attr_data>(new Data(data)), persistent);
        if (m_on_set)
            env2 = m_on_set(env2, ios, n, data, persistent);
        return env2;
    }
    std::shared_ptr<Data> get_data(environment const & env, name const & n) const {
        auto data = get(env, n);
        if (!data)
            return {};
        lean_assert(std::dynamic_pointer_cast<Data>(data));
        return std::static_pointer_cast<Data>(data);
    }
};

struct indices_attribute_data : public attr_data {
    list<unsigned> m_idxs;
    indices_attribute_data(list<unsigned> const & idxs) : m_idxs(idxs) {}
    indices_attribute_data() : indices_attribute_data(list<unsigned>()) {}

    virtual unsigned hash() const override {
        unsigned h = 0;
        for (unsigned i : m_idxs)
            h = ::lean::hash(h, i);
        return h;
    }
    void write(serializer & s) const {
        write_list(s, m_idxs);
    }
    void read(deserializer & d) {
        m_idxs = read_list<unsigned>(d);
    }
    virtual void print(std::ostream & out) override {
        for (auto p : m_idxs) {
            out << " " << p + 1;
        }
    }
};

/** \brief Attribute that represents a list of indices. input and output are 1-indexed for convenience. */
class indices_attribute : public typed_attribute<indices_attribute_data> {
public:
    indices_attribute(char const * id, char const * descr, on_set_proc on_set) : typed_attribute(id, descr, on_set) {}
    indices_attribute(char const * id, char const * descr) : typed_attribute(id, descr) {}

    virtual attr_data_ptr parse_data(abstract_parser &) const override;
};

void register_attribute(attribute_ptr);
attribute const & get_attribute(std::string const & attr);
void get_attributes(buffer<attribute const *> &);

template<typename Attribute>
void register_attribute(Attribute attr) {
    register_attribute(attribute_ptr(new Attribute(attr)));
}

void register_incompatible(char const * attr1, char const * attr2);

// TODO(sullrich): all of these should become members of/return attribute or a subclass
bool is_attribute(std::string const & attr);
void get_attribute_tokens(buffer<char const *> &);
attribute const * get_attribute_from_token(char const * attr_token);

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, unsigned prio, list<unsigned> const & params, bool persistent);
environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, bool persistent);

bool has_attribute(environment const & env, char const * attr, name const & d);
void get_attribute_instances(environment const & env, char const * attr, buffer<name> &);
priority_queue<name, name_quick_cmp> get_attribute_instances_by_prio(environment const & env, name const & attr);

unsigned get_attribute_prio(environment const & env, std::string const & attr, name const & d);
list<unsigned> get_attribute_params(environment const & env, std::string const & attr, name const & d);

bool are_incompatible(attribute const * attr1, attribute const * attr2);

void initialize_attribute_manager();
void finalize_attribute_manager();
}
