prelude

/-
Environment extensions:

- private
  * unsigned       mCounter
  * NameMap<Name> mInvMap;  // map: hidden-Name -> user-Name (for pretty printing purposes) it is serialized
  * NameSet       mPrivatePrefixes; // transient (it is used for registerPrivateName)

- protected
  * NameSet mProtected;

- noncomputable
  * NameSet

- exportDecl: it is used to implement the `export` command
  * NameMap<List<exportDecl>> mNsMap;   // mapping from namespace to "export Declaration"

- auxRecursors
  * NameSet mAuxRecursorSet;
  * NameSet mNoConfusionSet;

- aliases: this is a transient object used during elaboration. We use it to store the mappings (user-facing-Name -> private Name); implementing `open` command; simulating `section` parameters; etc.
  * Bool             mInSection;
  * NameMap<names>  mAliases;
  * NameMap<Name>   mInvAliases;
  * NameMap<Name>   mLevelAliases;
  * NameMap<Name>   mInvLevelAliases;
  * NameMap<Expr>   mLocalRefs;

- projection: it will be deleted

- user attributes:
  * NameMap<attributePtr> mAttrs;

- Bytecode
  * unsignedMap<vmDecl>           mDecls;
  * unsignedMap<vmCasesFunction> mCases;
  * Name                            mMonitor;

- Module
  *  std::vector<moduleName> mDirectImports;
  *  List<std::sharedPtr<modification const>> mModifications;
  *  names        mModuleUnivs;
  *  names        mModuleDecls;
  *  NameSet     mModuleDefs;
  *  NameSet     mImported;
  *  // Map from Declaration Name to olean file where it was defined
  *  NameMap<std::String>     mDecl2Olean;
  *  NameMap<posInfo>        mDecl2PosInfo;

- scopedExt: a general purpose scoped extension. It is used to implement
  * Parser/scanner tables
  * attributeManager (do we need them? we can try to keep user attributes only)
    * elaboration strategy
    * user commands
    * use annonymous Constructor when pretty printing
    * "parsing-only"
    * reducibility annotations
    * [inline]
    * [pattern]
    * [class]
    * [instance]
    * [recursor]
  * activeExportDecls
  * class
  * userRecursors
    * NameMap<recursorInfo> mRecursors;
    * NameMap<names>         mType2Recursors;
-/
