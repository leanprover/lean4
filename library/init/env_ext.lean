prelude

/-
Environment extensions:

- private
  * unsigned       mCounter
  * nameMap<name> mInvMap;  // map: hidden-name -> user-name (for pretty printing purposes) it is serialized
  * nameSet       mPrivatePrefixes; // transient (it is used for registerPrivateName)

- protected
  * nameSet mProtected;

- noncomputable
  * nameSet

- exportDecl: it is used to implement the `export` command
  * nameMap<list<exportDecl>> mNsMap;   // mapping from namespace to "export declaration"

- auxRecursors
  * nameSet mAuxRecursorSet;
  * nameSet mNoConfusionSet;

- aliases: this is a transient object used during elaboration. We use it to store the mappings (user-facing-name -> private name); implementing `open` command; simulating `section` parameters; etc.
  * bool             mInSection;
  * nameMap<names>  mAliases;
  * nameMap<name>   mInvAliases;
  * nameMap<name>   mLevelAliases;
  * nameMap<name>   mInvLevelAliases;
  * nameMap<expr>   mLocalRefs;

- projection: it will be deleted

- user attributes:
  * nameMap<attributePtr> mAttrs;

- Bytecode
  * unsignedMap<vmDecl>           mDecls;
  * unsignedMap<vmCasesFunction> mCases;
  * name                            mMonitor;

- module
  *  std::vector<moduleName> mDirectImports;
  *  list<std::sharedPtr<modification const>> mModifications;
  *  names        mModuleUnivs;
  *  names        mModuleDecls;
  *  nameSet     mModuleDefs;
  *  nameSet     mImported;
  *  // Map from declaration name to olean file where it was defined
  *  nameMap<std::string>     mDecl2Olean;
  *  nameMap<posInfo>        mDecl2PosInfo;

- scopedExt: a general purpose scoped extension. It is used to implement
  * parser/scanner tables
  * attributeManager (do we need them? we can try to keep user attributes only)
    * elaboration strategy
    * user commands
    * use annonymous constructor when pretty printing
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
    * nameMap<recursorInfo> mRecursors;
    * nameMap<names>         mType2Recursors;
-/
