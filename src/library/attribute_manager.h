/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
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
};

typedef std::shared_ptr<attr_data> attr_data_ptr;
struct attr_config;

class attribute {
    friend struct attr_config;
private:
    std::string m_id;
    std::string m_descr;
    std::string m_token;
protected:
    environment set_core(environment const &, io_state const &, name const &, attr_data_ptr, bool) const;
    virtual void write_entry(serializer &, attr_data const &) const = 0;
    virtual attr_data_ptr read_entry(deserializer &) const = 0;
public:
    attribute(char const * id, char const * descr) : m_id(id), m_descr(descr), m_token(std::string("[") + id) {}
    std::string const & get_name() const { return m_id; }
    std::string const & get_token() const { return m_token; }
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
    virtual attr_data_ptr read_entry(deserializer &) const override final { return {}; }
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
    virtual attr_data_ptr read_entry(deserializer &) const override final { return {}; }
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
};

struct unsigned_params_attribute_data : public attr_data {
    list<unsigned> m_params;
    unsigned_params_attribute_data(list<unsigned> const & params) : m_params(params) {}
    unsigned_params_attribute_data() : unsigned_params_attribute_data(list<unsigned>()) {}

    virtual unsigned hash() const override {
        unsigned h = 0;
        for (unsigned i : m_params)
            h = ::lean::hash(h, i);
        return h;
    }
    void write(serializer & s) const {
        write_list(s, m_params);
    }
    void read(deserializer & d) {
        m_params = read_list<unsigned>(d);
    }
};

template class typed_attribute<unsigned_params_attribute_data>;
typedef typed_attribute<unsigned_params_attribute_data> unsigned_params_attribute;

void register_attribute(attribute_ptr);

template<typename Attribute>
void register_attribute(Attribute attr) {
    register_attribute(attribute_ptr(new Attribute(attr)));
}

void register_incompatible(char const * attr1, char const * attr2);

// TODO(sullrich): all of these should become members of/return attribute or a subclass
bool is_attribute(std::string const & attr);
void get_attributes(buffer<char const *> &);
void get_attribute_tokens(buffer<char const *> &);
char const * get_attribute_from_token(char const * attr_token);
char const * get_attribute_token(char const * attr);

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, unsigned prio, list<unsigned> const & params, bool persistent);
environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, bool persistent);

bool has_attribute(environment const & env, char const * attr, name const & d);
void get_attribute_instances(environment const & env, name const & attr, buffer<name> &);
priority_queue<name, name_quick_cmp> get_attribute_instances_by_prio(environment const & env, name const & attr);

unsigned get_attribute_prio(environment const & env, std::string const & attr, name const & d);
list<unsigned> get_attribute_params(environment const & env, std::string const & attr, name const & d);

bool are_incompatible(char const * attr1, char const * attr2);

void initialize_attribute_manager();
void finalize_attribute_manager();
}
