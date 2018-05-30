prelude

/-
Environment extensions:

- inductive and quotient extensions will become part of the environment

- private
  * unsigned       m_counter
  * name_map<name> m_inv_map;  // map: hidden-name -> user-name (for pretty printing purposes) it is serialized
  * name_set       m_private_prefixes; // transient (it is used for register_private_name)

- protected
  * name_set m_protected;

- noncomputable
  * name_set

- export_decl: it is used to implement the `export` command
  * name_map<list<export_decl>> m_ns_map;   // mapping from namespace to "export declaration"

- aux_recursors
  * name_set m_aux_recursor_set;
  * name_set m_no_confusion_set;

- documentation
  * list<doc_entry>       m_module_doc;      // this is not used
  * name_map<std::string> m_doc_string_map;  // mapping declaration name to doc string

- ginductive: it will be deleted

- aliases: this is a transient object used during elaboration. We use it to store the mappings (user-facing-name -> private name); implementing `open` command; simulating `section` parameters; etc.
  * bool             m_in_section;
  * name_map<names>  m_aliases;
  * name_map<name>   m_inv_aliases;
  * name_map<name>   m_level_aliases;
  * name_map<name>   m_inv_level_aliases;
  * name_map<expr>   m_local_refs;

- projection: it will be deleted

- fingerprint: (we can store this information in the environment)
  * uint64 m_fingerprint

- eqn_lemmas: maps definition to its equational lemmas. It is used to implement tactics.
  * name_map<list<simp_lemma>> m_lemmas;
  * name_set                   m_has_simple_eqn_lemma;

- user attributes:
  * name_map<attribute_ptr> m_attrs;

- Bytecode
  * unsigned_map<vm_decl>           m_decls;
  * unsigned_map<vm_cases_function> m_cases;
  * name                            m_monitor;

- module
  *  std::vector<module_name> m_direct_imports;
  *  list<std::shared_ptr<modification const>> m_modifications;
  *  names        m_module_univs;
  *  names        m_module_decls;
  *  name_set     m_module_defs;
  *  name_set     m_imported;
  *  // Map from declaration name to olean file where it was defined
  *  name_map<std::string>     m_decl2olean;
  *  name_map<pos_info>        m_decl2pos_info;

- scoped_ext: a general purpose scoped extension. It is used to implement
  * parser/scanner tables
  * inverse (it can be deleted after we remove g_inductive)
  * attribute_manager (do we need them? we can try to keep user attributes only)
    * elaboration strategy
    * user commands
    * use annonymous constructor when pretty printing
    * "parsing-only"
    * reducibility annotations
    * [inline]
    * [pattern]
    * [inverse] (it can be deleted in the future)
    * [class]
    * [instance]
    * [recursor]
    * [simp]
    * [congr]
    * [refl]
    * [symm]
    * [trans]
  * active_export_decls
  * class
  * user_recursors
    * name_map<recursor_info> m_recursors;
    * name_map<names>         m_type2recursors;
  * relation_manager
-/
