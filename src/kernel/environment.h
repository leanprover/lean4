/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <memory>
#include "util/rc.h"
#include "util/optional.h"
#include "util/rb_map.h"
#include "kernel/expr.h"
#include "kernel/constraint.h"
#include "kernel/definition.h"

namespace lean {
class type_checker;
class environment;
class certified_definition;

/**
   \brief The Lean kernel can be instantiated with different normalization extensions.
   Each extension is part of the trusted code base. The extensions allow us to support
   different flavors of the core type theory. We will use these extensions to implement
   inductive datatype (ala Coq), HIT, record types, etc.
*/
class normalizer_extension {
public:
    virtual optional<std::pair<expr, constraints>> operator()(expr const & t, environment const & env, type_checker & tc) const;
};

/**
   \brief The header of an environment is created when we create the empty environment.
   Moreover if environment B is an extension of environment A, then A and B share the same header.
*/
class environment_header {
    /* In the following field, 0 means untrusted mode (i.e., check everything),
       >= 1 means do not check imported modules, and do not check macros
       with level less than the value of this field.
    */
    unsigned m_trust_lvl; //!the given one.
    bool m_proof_irrel;   //!< true if the kernel assumes proof irrelevance
    bool m_eta;           //!< true if the kernel uses eta-reduction in convertability checks
    std::unique_ptr<normalizer_extension const> m_norm_ext;
    void dealloc();
public:
    environment_header(unsigned trust_lvl, bool proof_irrel, bool eta, std::unique_ptr<normalizer_extension const> ext);
    unsigned trust_lvl() const { return m_trust_lvl; }
    bool proof_irrel() const { return m_proof_irrel; }
    bool eta() const { return m_eta; }
    normalizer_extension const & norm_ext() const { return *(m_norm_ext.get()); }
};

class environment_extension {
public:
    virtual ~environment_extension();
};

typedef std::vector<std::shared_ptr<environment_extension const>> environment_extensions;

/**
   \brief Lean core environment. An environment object can be extended/customized in different ways:

   1- By providing a normalizer_extension when creating an empty environment.
   2- By setting the proof_irrel and eta flags when creating an empty environment.
   3- By attaching additional data as environment::extensions. The additional data can be added
      at any time. They contain information used by the automation (e.g., rewriting sets, unification hints, etc).
*/
class environment {
    typedef std::shared_ptr<environment_header const>     header;
    typedef rb_map<name, definition, name_quick_cmp>      definitions;
    typedef std::shared_ptr<environment_extensions const> extensions;

    header      m_header;
    definitions m_definitions;
    extensions  m_extensions;

    environment(header const & h, definitions const & d, extensions const & ext);

public:
    environment(unsigned trust_lvl = 0, bool proof_irrel = true, bool eta = true);
    environment(unsigned trust_lvl, bool proof_irrel, bool eta, std::unique_ptr<normalizer_extension> ext);
    ~environment();

    std::shared_ptr<environment_header const> get_header() const { return m_header; }

    /** \brief Return the trust level of this environment. */
    unsigned trust_lvl() const { return m_header->trust_lvl(); }

    /** \brief Return true iff the environment assumes proof irrelevance */
    bool proof_irrel() const { return m_header->proof_irrel(); }

    /** \brief Return true iff the environment assumes Eta-reduction */
    bool eta() const { return m_header->eta(); }

    /** \brief Return reference to the normalizer extension associatied with this environment. */
    normalizer_extension const & norm_ext() const { return m_header->norm_ext(); }

    /** \brief Return definition with name \c n (if it is defined in this environment). */
    optional<definition> find(name const & n) const;

    /** \brief Return definition with name \c n. Throws and exception if definition does not exist in this environment. */
    definition get(name const & n) const;

    /**
       \brief Extends the current environment with the given (certified) definition
       This method throws an exception if:
          - The definition was certified in an environment which is not an ancestor of this one.
          - The environment already contains a definition with the given name.
    */
    environment add(certified_definition const & d) const;

    /**
       \brief Replace the axiom with name <tt>t.get_definition().get_name()</tt> with the theorem t.get_definition().
       This method throws an exception if:
          - The theorem was certified in an environment which is not an ancestor of this one.
          - The environment does not contain an axiom named <tt>t.get_definition().get_name()</tt>
    */
    environment replace(certified_definition const & t) const;

    /**
       \brief Register an environment extension. Every environment
       object may contain this extension. The argument \c initial is
       the initial value for the new extensions. The extension object
       can be retrieved using the given token (unsigned integer) returned
       by this method.

       \remark The extension objects are created on demand.

       \see get_extension
    */
    static unsigned register_extension(std::shared_ptr<environment_extension const> const & initial);

    /** \brief Return the extension with the given id. */
    environment_extension const & get_extension(unsigned extid) const;

    /** \brief Update the environment extension with the given id. */
    environment update(unsigned extid, std::shared_ptr<environment_extension const> const & ext) const;
};

/**
   \brief A certified definition is one that has been type checked.
   Only the type_checker class can create certified definitions.
*/
class certified_definition {
    friend class type_checker;
    std::shared_ptr<environment_header const> m_header;
    definition                                m_definition;
    certified_definition(std::shared_ptr<environment_header const> const & h, definition const & d);
public:
    certified_definition(certified_definition const & c);
    std::shared_ptr<environment_header const> const & get_header() const { return m_header; }
    definition const & get_definition() const { return m_definition; }
};
}
