// Lean compiler output
// Module: Lake.DSL.Syntax
// Imports: Lake.DSL.DeclUtil Lean.Parser.Term
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lake_DSL_facetSuffix___closed__5;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_depSpec;
static lean_object* l_Lake_DSL_inputFileCommand___closed__3;
static lean_object* l_Lake_DSL_fromGit___closed__8;
static lean_object* l_Lake_DSL_withClause___closed__3;
static lean_object* l_Lake_DSL_depSpec___closed__2;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__1;
static lean_object* l_Lake_DSL_inputDirCommand___closed__0;
static lean_object* l_Lake_DSL_metaIf___closed__4;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_fromClause;
static lean_object* l_Lake_DSL_buildDeclSig___closed__3;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__12;
LEAN_EXPORT lean_object* l_Lake_DSL_runIO;
static lean_object* l_Lake_DSL_packageCommand___closed__16;
static lean_object* l_Lake_DSL_requireDecl___closed__6;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__3;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__10;
static lean_object* l_Lake_DSL_fromClause___closed__5;
static lean_object* l_Lake_DSL_depName___closed__2;
static lean_object* l_Lake_DSL_getConfig___closed__1;
static lean_object* l_Lake_DSL_packageCommand___closed__22;
static lean_object* l_Lake_DSL_getConfig___closed__7;
static lean_object* l_Lake_DSL_externLibDeclSpec___closed__1;
static lean_object* l_Lake_verLit___closed__8;
static lean_object* l_Lake_DSL_verSpec___closed__3;
static lean_object* l_Lake_DSL_verClause___closed__2;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__15;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__5;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__8;
static lean_object* l_Lake_DSL_runIO___closed__3;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__13;
LEAN_EXPORT lean_object* l_Lake_DSL_leanExeCommand;
static lean_object* l_Lake_DSL_cmdDo___closed__8;
static lean_object* l_Lake_DSL_scriptDecl___closed__6;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__3;
static lean_object* l_Lake_verLit___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_requireDecl;
static lean_object* l_Lake_DSL_packageCommand___closed__12;
static lean_object* l_Lake_DSL_fromClause___closed__1;
static lean_object* l_Lake_DSL_facetSuffix___closed__2;
static lean_object* l_Lake_DSL_dirConst___closed__2;
extern lean_object* l_Lake_DSL_simpleBinder;
static lean_object* l_Lake_DSL_depSpec___closed__8;
static lean_object* l_Lake_DSL_cmdDo___closed__6;
static lean_object* l_Lake_DSL_cmdDo___closed__13;
static lean_object* l_Lake_DSL_depSpec___closed__7;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__14;
static lean_object* l_Lake_DSL_inputFileCommand___closed__5;
extern lean_object* l_Lake_DSL_optConfig;
static lean_object* l_Lake_verLit___closed__2;
static lean_object* l_Lake_DSL_cmdDo___closed__7;
static lean_object* l_Lake_DSL_packageCommand___closed__0;
static lean_object* l_Lake_DSL_fromClause___closed__0;
static lean_object* l_Lake_DSL_runIO___closed__6;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__18;
static lean_object* l_Lake_DSL_packageCommand___closed__5;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_verSpec;
static lean_object* l_Lake_DSL_runIO___closed__8;
static lean_object* l_Lake_DSL_packageCommand___closed__8;
static lean_object* l_Lake_DSL_fromGit___closed__2;
static lean_object* l_Lake_DSL_verSpec___closed__1;
extern lean_object* l_Lake_DSL_identOrStr;
LEAN_EXPORT lean_object* l_Lake_DSL_packageCommand;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__1;
static lean_object* l_Lake_DSL_facetSuffix___closed__6;
static lean_object* l_Lake_DSL_buildDeclSig___closed__1;
static lean_object* l_Lake_DSL_metaIf___closed__7;
static lean_object* l_Lake_DSL_buildDeclSig___closed__8;
static lean_object* l_Lake_DSL_dirConst___closed__3;
static lean_object* l_Lake_DSL_scriptDecl___closed__0;
static lean_object* l_Lake_DSL_requireDecl___closed__5;
static lean_object* l_Lake_DSL_depName___closed__13;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__8;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__4;
static lean_object* l_Lake_DSL_targetCommand___closed__0;
static lean_object* l_Lake_DSL_buildDeclSig___closed__5;
static lean_object* l_Lake_DSL_runIO___closed__5;
static lean_object* l_Lake_DSL_depName___closed__8;
static lean_object* l_Lake_DSL_packageCommand___closed__1;
static lean_object* l_Lake_DSL_inputDirCommand___closed__3;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__0;
static lean_object* l_Lake_DSL_leanExeCommand___closed__1;
static lean_object* l_Lake_DSL_leanExeCommand___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_cmdDo;
static lean_object* l_Lake_DSL_fromGit___closed__12;
static lean_object* l_Lake_DSL_metaIf___closed__15;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__2;
static lean_object* l_Lake_DSL_dirConst___closed__5;
static lean_object* l_Lake_DSL_scriptDecl___closed__2;
static lean_object* l_Lake_DSL_fromGit___closed__5;
static lean_object* l_Lake_DSL_verClause___closed__1;
static lean_object* l_Lake_DSL_inputFileCommand___closed__2;
static lean_object* l_Lake_DSL_requireDecl___closed__2;
static lean_object* l_Lake_DSL_leanExeCommand___closed__0;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__8;
static lean_object* l_Lake_DSL_depName___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_packageCommand___closed__20;
static lean_object* l_Lake_DSL_cmdDo___closed__14;
static lean_object* l_Lake_DSL_metaIf___closed__6;
static lean_object* l_Lake_DSL_inputFileCommand___closed__1;
static lean_object* l_Lake_DSL_fromSource___closed__3;
static lean_object* l_Lake_DSL_fromPath___closed__5;
static lean_object* l_Lake_DSL_metaIf___closed__8;
static lean_object* l_Lake_DSL_fromPath___closed__4;
static lean_object* l_Lake_DSL_packageCommand___closed__3;
static lean_object* l_Lake_verLit___closed__3;
static lean_object* l_Lake_DSL_leanLibCommand___closed__0;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__7;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__17;
static lean_object* l_Lake_DSL_depSpec___closed__5;
static lean_object* l_Lake_DSL_fromGit___closed__0;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__0;
static lean_object* l_Lake_DSL_cmdDo___closed__5;
static lean_object* l_Lake_DSL_scriptDeclSpec___closed__2;
static lean_object* l_Lake_DSL_getConfig___closed__6;
static lean_object* l_Lake_DSL_leanLibCommand___closed__6;
static lean_object* l_Lake_DSL_cmdDo___closed__12;
static lean_object* l_Lake_DSL_depSpec___closed__0;
LEAN_EXPORT lean_object* l_Lake_DSL_packageTargetLit;
static lean_object* l_Lake_DSL_fromSource___closed__0;
static lean_object* l_Lake_DSL_metaIf___closed__16;
static lean_object* l_Lake_DSL_packageCommand___closed__14;
static lean_object* l_Lake_DSL_scriptDeclSpec___closed__0;
static lean_object* l_Lake_DSL_cmdDo___closed__1;
static lean_object* l_Lake_DSL_depName___closed__9;
static lean_object* l_Lake_DSL_fromGit___closed__14;
static lean_object* l_Lake_DSL_scriptDeclSpec___closed__1;
static lean_object* l_Lake_DSL_verClause___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_getConfig;
static lean_object* l_Lake_DSL_fromPath___closed__1;
static lean_object* l_Lake_DSL_metaIf___closed__11;
static lean_object* l_Lake_DSL_dirConst___closed__0;
static lean_object* l_Lake_DSL_packageCommand___closed__21;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__0;
static lean_object* l_Lake_DSL_packageTargetLit___closed__4;
static lean_object* l_Lake_DSL_runIO___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_packageFacetDecl;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__5;
static lean_object* l_Lake_DSL_fromGit___closed__6;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_postUpdateDecl;
static lean_object* l_Lake_DSL_packageTargetLit___closed__6;
static lean_object* l_Lake_DSL_facetSuffix___closed__0;
static lean_object* l_Lake_DSL_fromGit___closed__3;
static lean_object* l_Lake_verLit___closed__11;
static lean_object* l_Lake_verLit___closed__9;
static lean_object* l_Lake_DSL_fromGit___closed__10;
static lean_object* l_Lake_DSL_inputDirCommand___closed__2;
static lean_object* l_Lake_DSL_metaIf___closed__9;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__9;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__16;
LEAN_EXPORT lean_object* l_Lake_DSL_term_x60_x40_______x2f________;
static lean_object* l_Lake_DSL_inputFileCommand___closed__7;
static lean_object* l_Lake_verLit___closed__12;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__4;
static lean_object* l_Lake_DSL_metaIf___closed__1;
static lean_object* l_Lake_DSL_buildDeclSig___closed__0;
LEAN_EXPORT lean_object* l_Lake_DSL_facetSuffix;
static lean_object* l_Lake_DSL_leanExeCommand___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_scriptDeclSpec;
static lean_object* l_Lake_DSL_metaIf___closed__3;
static lean_object* l_Lake_DSL_cmdDo___closed__0;
static lean_object* l_Lake_DSL_getConfig___closed__8;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__1;
static lean_object* l_Lake_DSL_packageCommand___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_inputDirCommand;
static lean_object* l_Lake_DSL_inputDirCommand___closed__7;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__1;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__5;
static lean_object* l_Lake_DSL_metaIf___closed__12;
static lean_object* l_Lake_DSL_externLibDeclSpec___closed__0;
static lean_object* l_Lake_verLit___closed__1;
LEAN_EXPORT lean_object* l_Lake_verLit;
static lean_object* l_Lake_DSL_dirConst___closed__6;
static lean_object* l_Lake_DSL_buildDeclSig___closed__2;
static lean_object* l_Lake_DSL_verSpec___closed__4;
static lean_object* l_Lake_DSL_cmdDo___closed__10;
static lean_object* l_Lake_DSL_metaIf___closed__0;
static lean_object* l_Lake_DSL_depName___closed__0;
static lean_object* l_Lake_DSL_cmdDo___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_fromGit;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__2;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__2;
static lean_object* l_Lake_DSL_packageCommand___closed__13;
static lean_object* l_Lake_DSL_externLibCommand___closed__4;
static lean_object* l_Lake_DSL_facetSuffix___closed__1;
static lean_object* l_Lake_DSL_depName___closed__12;
static lean_object* l_Lake_DSL_runIO___closed__4;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__0;
static lean_object* l_Lake_DSL_getConfig___closed__10;
static lean_object* l_Lake_DSL_leanLibCommand___closed__1;
static lean_object* l_Lake_DSL_getConfig___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_externLibCommand;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__6;
static lean_object* l_Lake_DSL_packageTargetLit___closed__5;
static lean_object* l_Lake_DSL_getConfig___closed__5;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__0;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__14;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__1;
static lean_object* l_Lake_DSL_fromGit___closed__16;
static lean_object* l_Lake_DSL_packageCommand___closed__4;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__19;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__6;
static lean_object* l_Lake_DSL_withClause___closed__5;
static lean_object* l_Lake_DSL_inputDirCommand___closed__1;
static lean_object* l_Lake_DSL_buildDeclSig___closed__4;
static lean_object* l_Lake_DSL_depSpec___closed__6;
static lean_object* l_Lake_DSL_packageTargetLit___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_inputFileCommand;
static lean_object* l_Lake_DSL_requireDecl___closed__4;
static lean_object* l_Lake_DSL_packageCommand___closed__10;
static lean_object* l_Lake_DSL_inputFileCommand___closed__0;
static lean_object* l_Lake_DSL_fromClause___closed__4;
static lean_object* l_Lake_DSL_buildDeclSig___closed__6;
static lean_object* l_Lake_DSL_withClause___closed__0;
static lean_object* l_Lake_DSL_packageTargetLit___closed__3;
static lean_object* l_Lake_DSL_leanLibCommand___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_fromSource;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__12;
static lean_object* l_Lake_DSL_depName___closed__7;
static lean_object* l_Lake_DSL_scriptDecl___closed__3;
static lean_object* l_Lake_DSL_inputFileCommand___closed__4;
static lean_object* l_Lake_DSL_scriptDecl___closed__4;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__7;
static lean_object* l_Lake_DSL_metaIf___closed__17;
static lean_object* l_Lake_DSL_cmdDo___closed__4;
static lean_object* l_Lake_DSL_fromGit___closed__1;
static lean_object* l_Lake_DSL_packageCommand___closed__18;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__10;
static lean_object* l_Lake_DSL_targetCommand___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_fromPath;
extern lean_object* l_Lake_DSL_declValDo;
static lean_object* l_Lake_DSL_packageCommand___closed__19;
static lean_object* l_Lake_DSL_scriptDecl___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_moduleFacetDecl;
static lean_object* l_Lake_DSL_depName___closed__3;
static lean_object* l_Lake_DSL_inputDirCommand___closed__4;
static lean_object* l_Lake_DSL_fromGit___closed__15;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__0;
static lean_object* l_Lake_DSL_packageTargetLit___closed__2;
static lean_object* l_Lake_DSL_withClause___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_scriptDecl;
static lean_object* l_Lake_DSL_packageCommand___closed__11;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__4;
static lean_object* l_Lake_DSL_packageCommand___closed__17;
static lean_object* l_Lake_DSL_fromGit___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_leanLibCommand;
static lean_object* l_Lake_verLit___closed__10;
static lean_object* l_Lake_DSL_cmdDo___closed__15;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__7;
static lean_object* l_Lake_DSL_fromGit___closed__13;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__6;
static lean_object* l_Lake_DSL_getConfig___closed__0;
static lean_object* l_Lake_DSL_packageCommand___closed__7;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__11;
LEAN_EXPORT lean_object* l_Lake_DSL_libraryFacetDecl;
static lean_object* l_Lake_DSL_fromClause___closed__3;
static lean_object* l_Lake_DSL_depName___closed__5;
static lean_object* l_Lake_DSL_cmdDo___closed__9;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__4;
static lean_object* l_Lake_DSL_externLibCommand___closed__2;
static lean_object* l_Lake_DSL_inputFileCommand___closed__6;
static lean_object* l_Lake_verLit___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_externLibDeclSpec;
static lean_object* l_Lake_DSL_fromPath___closed__2;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__15;
static lean_object* l_Lake_DSL_verSpec___closed__0;
static lean_object* l_Lake_DSL_packageCommand___closed__2;
static lean_object* l_Lake_DSL_getConfig___closed__2;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__9;
static lean_object* l_Lake_DSL_verClause___closed__3;
static lean_object* l_Lake_DSL_metaIf___closed__10;
LEAN_EXPORT lean_object* l_Lake_DSL_targetCommand;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_getConfig___closed__3;
static lean_object* l_Lake_DSL_depName___closed__6;
static lean_object* l_Lake_DSL_facetSuffix___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_depName;
static lean_object* l_Lake_DSL_externLibCommand___closed__0;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__1;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__3;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__6;
static lean_object* l_Lake_DSL_buildDeclSig___closed__7;
static lean_object* l_Lake_DSL_fromGit___closed__7;
static lean_object* l_Lake_DSL_fromGit___closed__11;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__9;
static lean_object* l_Lake_DSL_targetCommand___closed__2;
static lean_object* l_Lake_DSL_packageTargetLit___closed__8;
static lean_object* l_Lake_DSL_facetSuffix___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_term_x60_x2b______;
LEAN_EXPORT lean_object* l_Lake_DSL_buildDeclSig;
static lean_object* l_Lake_DSL_fromGit___closed__4;
static lean_object* l_Lake_DSL_runIO___closed__0;
static lean_object* l_Lake_DSL_leanExeCommand___closed__4;
static lean_object* l_Lake_DSL_dirConst___closed__4;
static lean_object* l_Lake_DSL_fromPath___closed__0;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__5;
static lean_object* l_Lake_DSL_inputDirCommand___closed__5;
static lean_object* l_Lake_DSL_withClause___closed__4;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__4;
static lean_object* l_Lake_DSL_packageFacetDecl___closed__3;
static lean_object* l_Lake_DSL_externLibCommand___closed__1;
static lean_object* l_Lake_DSL_depName___closed__1;
static lean_object* l_Lake_DSL_dirConst___closed__1;
static lean_object* l_Lake_DSL_leanLibCommand___closed__2;
static lean_object* l_Lake_DSL_inputDirCommand___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_metaIf;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__16;
static lean_object* l_Lake_DSL_externLibCommand___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_dirConst;
static lean_object* l_Lake_DSL_fromSource___closed__2;
static lean_object* l_Lake_DSL_verClause___closed__4;
static lean_object* l_Lake_DSL_leanLibCommand___closed__4;
static lean_object* l_Lake_DSL_externLibCommand___closed__5;
static lean_object* l_Lake_DSL_withClause___closed__1;
static lean_object* l_Lake_DSL_packageTargetLit___closed__0;
static lean_object* l_Lake_DSL_packageCommand___closed__15;
static lean_object* l_Lake_DSL_cmdDo___closed__11;
static lean_object* l_Lake_verLit___closed__0;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__11;
static lean_object* l_Lake_DSL_scriptDeclSpec___closed__3;
static lean_object* l_Lake_DSL_libraryFacetDecl___closed__5;
static lean_object* l_Lake_DSL_leanExeCommand___closed__5;
static lean_object* l_Lake_DSL_externLibDeclSpec___closed__3;
static lean_object* l_Lake_DSL_verSpec___closed__2;
static lean_object* l_Lake_DSL_fromPath___closed__3;
static lean_object* l_Lake_DSL_metaIf___closed__13;
static lean_object* l_Lake_DSL_leanExeCommand___closed__7;
static lean_object* l_Lake_DSL_metaIf___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_withClause;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_DSL_leanLibCommand___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_metaIf___closed__14;
static lean_object* l_Lake_DSL_depSpec___closed__3;
static lean_object* l_Lake_DSL_scriptDecl___closed__5;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__5;
static lean_object* l_Lake_DSL_runIO___closed__2;
static lean_object* l_Lake_DSL_packageCommand___closed__9;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__10;
static lean_object* l_Lake_DSL_metaIf___closed__2;
static lean_object* l_Lake_DSL_getConfig___closed__4;
static lean_object* l_Lake_DSL_facetSuffix___closed__7;
static lean_object* l_Lake_DSL_requireDecl___closed__0;
LEAN_EXPORT lean_object* l_Lake_DSL_verClause;
static lean_object* l_Lake_DSL_moduleFacetDecl___closed__2;
static lean_object* l_Lake_DSL_depSpec___closed__1;
static lean_object* l_Lake_DSL_depName___closed__11;
static lean_object* l_Lake_DSL_requireDecl___closed__1;
static lean_object* l_Lake_DSL_depSpec___closed__4;
static lean_object* l_Lake_DSL_runIO___closed__7;
static lean_object* l_Lake_DSL_targetCommand___closed__6;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__3;
static lean_object* l_Lake_DSL_postUpdateDecl___closed__13;
static lean_object* l_Lake_DSL_cmdDo___closed__2;
static lean_object* l_Lake_DSL_externLibDeclSpec___closed__2;
static lean_object* l_Lake_verLit___closed__4;
static lean_object* l_Lake_DSL_targetCommand___closed__4;
static lean_object* l_Lake_verLit___closed__6;
static lean_object* l_Lake_DSL_fromSource___closed__1;
static lean_object* l_Lake_DSL_requireDecl___closed__3;
static lean_object* l_Lake_DSL_depName___closed__10;
static lean_object* l_Lake_DSL_packageTargetLit___closed__1;
static lean_object* l_Lake_DSL_leanLibCommand___closed__5;
static lean_object* l_Lake_DSL_targetCommand___closed__5;
static lean_object* l_Lake_DSL_leanExeCommand___closed__6;
static lean_object* l_Lake_DSL_term_x60_x2b_________closed__2;
static lean_object* l_Lake_DSL_term_x60_x40_______x2f___________closed__6;
static lean_object* l_Lake_DSL_verClause___closed__0;
static lean_object* l_Lake_DSL_externLibCommand___closed__3;
static lean_object* l_Lake_DSL_targetCommand___closed__1;
static lean_object* l_Lake_DSL_fromClause___closed__2;
static lean_object* _init_l_Lake_DSL_dirConst___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_dirConst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DSL", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_dirConst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dirConst", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_dirConst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_dirConst___closed__2;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_dirConst___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("__dir__", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_dirConst___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_dirConst___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_dirConst___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_dirConst___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lake_DSL_dirConst___closed__3;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_dirConst() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_dirConst___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("getConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_getConfig___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get_config\? ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_getConfig___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_getConfig___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_getConfig___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__8;
x_2 = l_Lake_DSL_getConfig___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_getConfig___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__9;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_getConfig___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_getConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_getConfig___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packageCommand", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optional", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageCommand___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("docComment", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageCommand___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageCommand___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_packageCommand___closed__6;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attributes", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_packageCommand___closed__11;
x_2 = l_Lake_DSL_packageCommand___closed__10;
x_3 = l_Lake_DSL_packageCommand___closed__9;
x_4 = l_Lake_DSL_packageCommand___closed__8;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageCommand___closed__12;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_packageCommand___closed__13;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__14;
x_2 = l_Lake_DSL_packageCommand___closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageCommand___closed__16;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__17;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_identOrStr;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__19;
x_2 = l_Lake_DSL_packageCommand___closed__18;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_optConfig;
x_2 = l_Lake_DSL_packageCommand___closed__20;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__21;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_packageCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_packageCommand___closed__22;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("postUpdateDecl", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("post_update ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppSpace", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_simpleBinder;
x_2 = l_Lake_DSL_postUpdateDecl___closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__8;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__9;
x_2 = l_Lake_DSL_postUpdateDecl___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declValSimple", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__14;
x_2 = l_Lake_DSL_postUpdateDecl___closed__13;
x_3 = l_Lake_DSL_packageCommand___closed__9;
x_4 = l_Lake_DSL_packageCommand___closed__8;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__15;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValDo;
x_2 = l_Lake_DSL_postUpdateDecl___closed__16;
x_3 = l_Lake_DSL_postUpdateDecl___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__17;
x_2 = l_Lake_DSL_postUpdateDecl___closed__10;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__18;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_postUpdateDecl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__19;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fromPath", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_fromPath___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_DSL_fromPath___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__4;
x_2 = l_Lake_DSL_fromPath___closed__1;
x_3 = l_Lake_DSL_fromPath___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromPath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_fromPath___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fromGit", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_fromGit___closed__2;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1024u);
x_2 = l_Lake_DSL_fromPath___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_fromGit___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__8;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__9;
x_2 = l_Lake_DSL_fromGit___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_fromGit___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__12;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__13;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__14;
x_2 = l_Lake_DSL_fromGit___closed__10;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__15;
x_2 = l_Lake_DSL_fromGit___closed__1;
x_3 = l_Lake_DSL_fromGit___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_fromGit___closed__16;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromSource___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fromSource", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromSource___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromSource___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath;
x_2 = l_Lake_DSL_fromGit;
x_3 = l_Lake_DSL_postUpdateDecl___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromSource___closed__2;
x_2 = l_Lake_DSL_fromSource___closed__1;
x_3 = l_Lake_DSL_fromSource___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromSource() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_fromSource___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromClause___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fromClause", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromClause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromClause___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromClause___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" from ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromClause___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_fromClause___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_fromClause___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromSource;
x_2 = l_Lake_DSL_fromClause___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromClause___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromClause___closed__4;
x_2 = l_Lake_DSL_fromClause___closed__1;
x_3 = l_Lake_DSL_fromClause___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromClause() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_fromClause___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_withClause___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withClause", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_withClause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_withClause___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_withClause___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" with ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_withClause___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_withClause___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_withClause___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__4;
x_2 = l_Lake_DSL_withClause___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_withClause___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_withClause___closed__4;
x_2 = l_Lake_DSL_withClause___closed__1;
x_3 = l_Lake_DSL_withClause___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_withClause() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_withClause___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_verSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("verSpec", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_verSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_verSpec___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_verSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_verSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_verSpec___closed__2;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_verSpec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_verSpec___closed__3;
x_2 = l_Lake_DSL_verSpec___closed__1;
x_3 = l_Lake_DSL_verSpec___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_verSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_verSpec___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_verClause___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("verClause", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_verClause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_verClause___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_verClause___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_verClause___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_verClause___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_verClause___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_verSpec;
x_2 = l_Lake_DSL_verClause___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_verClause___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_verClause___closed__4;
x_2 = l_Lake_DSL_verClause___closed__1;
x_3 = l_Lake_DSL_verClause___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_verClause() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_verClause___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depName", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depName___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("atomic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depName___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depName___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depName___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" / ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depName___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depName___closed__8;
x_2 = l_Lake_DSL_depName___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_depName___closed__9;
x_2 = l_Lake_DSL_depName___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_depName___closed__10;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr;
x_2 = l_Lake_DSL_depName___closed__11;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depName___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depName___closed__12;
x_2 = l_Lake_DSL_depName___closed__1;
x_3 = l_Lake_DSL_depName___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_depName___closed__13;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depSpec", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_verClause;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__2;
x_2 = l_Lake_DSL_depName;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromClause;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__4;
x_2 = l_Lake_DSL_depSpec___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_withClause;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__6;
x_2 = l_Lake_DSL_depSpec___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__7;
x_2 = l_Lake_DSL_depSpec___closed__1;
x_3 = l_Lake_DSL_depSpec___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_depSpec___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("requireDecl", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_requireDecl___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("require ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_requireDecl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_requireDecl___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec;
x_2 = l_Lake_DSL_requireDecl___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_requireDecl___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_requireDecl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_requireDecl___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildDeclSig", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__9;
x_2 = l_Lake_DSL_identOrStr;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeSpec", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_buildDeclSig___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__10;
x_3 = l_Lake_DSL_packageCommand___closed__9;
x_4 = l_Lake_DSL_packageCommand___closed__8;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_buildDeclSig___closed__4;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig___closed__5;
x_2 = l_Lake_DSL_buildDeclSig___closed__2;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__16;
x_2 = l_Lake_DSL_buildDeclSig___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig___closed__7;
x_2 = l_Lake_DSL_buildDeclSig___closed__1;
x_3 = l_Lake_DSL_buildDeclSig___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_buildDeclSig___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleFacetDecl", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_moduleFacetDecl___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module_facet ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_moduleFacetDecl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_moduleFacetDecl___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig;
x_2 = l_Lake_DSL_moduleFacetDecl___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_moduleFacetDecl___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_moduleFacetDecl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_moduleFacetDecl___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packageFacetDecl", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageFacetDecl___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package_facet ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageFacetDecl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageFacetDecl___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig;
x_2 = l_Lake_DSL_packageFacetDecl___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageFacetDecl___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_packageFacetDecl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_packageFacetDecl___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libraryFacetDecl", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_libraryFacetDecl___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("library_facet ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_libraryFacetDecl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_libraryFacetDecl___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig;
x_2 = l_Lake_DSL_libraryFacetDecl___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_libraryFacetDecl___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_libraryFacetDecl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_libraryFacetDecl___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("targetCommand", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_targetCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_targetCommand___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_targetCommand___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_buildDeclSig;
x_2 = l_Lake_DSL_targetCommand___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_targetCommand___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_targetCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_targetCommand___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanLibCommand", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_leanLibCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_leanLibCommand___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_leanLibCommand___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__19;
x_2 = l_Lake_DSL_leanLibCommand___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_optConfig;
x_2 = l_Lake_DSL_leanLibCommand___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_leanLibCommand___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_leanLibCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_leanLibCommand___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanExeCommand", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_leanExeCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_exe ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_leanExeCommand___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_leanExeCommand___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__19;
x_2 = l_Lake_DSL_leanExeCommand___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_optConfig;
x_2 = l_Lake_DSL_leanExeCommand___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_leanExeCommand___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_leanExeCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_leanExeCommand___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputFileCommand", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_inputFileCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input_file ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_inputFileCommand___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_inputFileCommand___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__19;
x_2 = l_Lake_DSL_inputFileCommand___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_optConfig;
x_2 = l_Lake_DSL_inputFileCommand___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_inputFileCommand___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_inputFileCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_inputFileCommand___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputDirCommand", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_inputDirCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input_dir ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_inputDirCommand___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_inputDirCommand___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageCommand___closed__19;
x_2 = l_Lake_DSL_inputDirCommand___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_optConfig;
x_2 = l_Lake_DSL_inputDirCommand___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_inputDirCommand___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_inputDirCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_inputDirCommand___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("externLibDeclSpec", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_externLibDeclSpec___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__16;
x_2 = l_Lake_DSL_buildDeclSig___closed__2;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_externLibDeclSpec___closed__2;
x_2 = l_Lake_DSL_externLibDeclSpec___closed__1;
x_3 = l_Lake_DSL_externLibDeclSpec___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_externLibDeclSpec___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("externLibCommand", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_externLibCommand___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extern_lib ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_externLibCommand___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_externLibCommand___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_externLibDeclSpec;
x_2 = l_Lake_DSL_externLibCommand___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_externLibCommand___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_externLibCommand___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_externLibCommand___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scriptDeclSpec", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_scriptDeclSpec___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_postUpdateDecl___closed__17;
x_2 = l_Lake_DSL_buildDeclSig___closed__2;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_scriptDeclSpec___closed__2;
x_2 = l_Lake_DSL_scriptDeclSpec___closed__1;
x_3 = l_Lake_DSL_scriptDeclSpec___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_scriptDeclSpec___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scriptDecl", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_scriptDecl___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("script ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_scriptDecl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_scriptDecl___closed__3;
x_2 = l_Lake_DSL_packageCommand___closed__15;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_scriptDeclSpec;
x_2 = l_Lake_DSL_scriptDecl___closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_scriptDecl___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_scriptDecl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_scriptDecl___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lake_verLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("verLit", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_verLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_verLit___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_verLit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("v!", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_verLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_verLit___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_verLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noWs", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_verLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_verLit___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_verLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_verLit___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_verLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__6;
x_2 = l_Lake_verLit___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_verLit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_verLit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_verLit___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_verLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromPath___closed__4;
x_2 = l_Lake_verLit___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_verLit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__10;
x_2 = l_Lake_verLit___closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_verLit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__11;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lake_verLit___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_verLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_verLit___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("facetSuffix", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_facetSuffix___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_facetSuffix___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__6;
x_2 = l_Lake_DSL_facetSuffix___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_facetSuffix___closed__4;
x_2 = l_Lake_DSL_depName___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__8;
x_2 = l_Lake_DSL_facetSuffix___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_facetSuffix___closed__6;
x_2 = l_Lake_DSL_facetSuffix___closed__1;
x_3 = l_Lake_DSL_facetSuffix___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_facetSuffix___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packageTargetLit", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageTargetLit___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_packageTargetLit___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__6;
x_2 = l_Lake_DSL_packageTargetLit___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_packageTargetLit___closed__4;
x_2 = l_Lake_DSL_depName___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_packageTargetLit___closed__5;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__8;
x_2 = l_Lake_DSL_packageTargetLit___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageTargetLit___closed__7;
x_2 = l_Lake_DSL_packageTargetLit___closed__1;
x_3 = l_Lake_DSL_packageTargetLit___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_packageTargetLit___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term`+___", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x2b_________closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`+", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_term_x60_x2b_________closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__6;
x_2 = l_Lake_DSL_term_x60_x2b_________closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__8;
x_2 = l_Lake_DSL_term_x60_x2b_________closed__4;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_term_x60_x2b_________closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_facetSuffix;
x_2 = l_Lake_DSL_term_x60_x2b_________closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x2b_________closed__8;
x_2 = l_Lake_DSL_term_x60_x2b_________closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b_________closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x2b_________closed__9;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lake_DSL_term_x60_x2b_________closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b______() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_term_x60_x2b_________closed__10;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term`@___/____", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_getConfig___closed__8;
x_2 = l_Lake_verLit___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__4;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__5;
x_2 = l_Lake_DSL_term_x60_x40_______x2f___________closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__12;
x_2 = l_Lake_verLit___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_verLit___closed__6;
x_2 = l_Lake_DSL_term_x60_x40_______x2f___________closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__8;
x_2 = l_Lake_DSL_depName___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_packageTargetLit;
x_2 = l_Lake_DSL_term_x60_x40_______x2f___________closed__9;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__10;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__11;
x_2 = l_Lake_DSL_term_x60_x40_______x2f___________closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_facetSuffix;
x_2 = l_Lake_verLit___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__13;
x_2 = l_Lake_DSL_term_x60_x2b_________closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__14;
x_2 = l_Lake_DSL_term_x60_x40_______x2f___________closed__12;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__15;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lake_DSL_term_x60_x40_______x2f___________closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f________() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_term_x60_x40_______x2f___________closed__16;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cmdDo", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_cmdDo___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_cmdDo___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("do", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_cmdDo___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many1Indent", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_cmdDo___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_cmdDo___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_DSL_cmdDo___closed__9;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_cmdDo___closed__10;
x_2 = l_Lake_DSL_cmdDo___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_cmdDo___closed__11;
x_2 = l_Lake_DSL_cmdDo___closed__5;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_cmdDo___closed__12;
x_2 = l_Lake_DSL_cmdDo___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_cmdDo___closed__10;
x_2 = l_Lake_DSL_cmdDo___closed__13;
x_3 = l_Lake_DSL_postUpdateDecl___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_cmdDo___closed__14;
x_2 = l_Lake_DSL_cmdDo___closed__1;
x_3 = l_Lake_DSL_cmdDo___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_cmdDo___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("metaIf", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_metaIf___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("meta ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_metaIf___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("if ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_metaIf___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_metaIf___closed__5;
x_2 = l_Lake_DSL_metaIf___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__4;
x_2 = l_Lake_DSL_metaIf___closed__6;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" then ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_metaIf___closed__8;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_metaIf___closed__9;
x_2 = l_Lake_DSL_metaIf___closed__7;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_cmdDo;
x_2 = l_Lake_DSL_metaIf___closed__10;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" else ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_metaIf___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_cmdDo;
x_2 = l_Lake_DSL_metaIf___closed__13;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_metaIf___closed__14;
x_2 = l_Lake_DSL_packageCommand___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_metaIf___closed__15;
x_2 = l_Lake_DSL_metaIf___closed__11;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_metaIf___closed__16;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_metaIf___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_metaIf() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_metaIf___closed__17;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runIO", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_runIO___closed__0;
x_2 = l_Lake_DSL_dirConst___closed__1;
x_3 = l_Lake_DSL_dirConst___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("run_io ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_runIO___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("doSeq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_runIO___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_runIO___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_runIO___closed__6;
x_2 = l_Lake_DSL_runIO___closed__3;
x_3 = l_Lake_DSL_getConfig___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_runIO___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_runIO___closed__7;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_runIO___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_runIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_runIO___closed__8;
return x_1;
}
}
lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_dirConst___closed__0 = _init_l_Lake_DSL_dirConst___closed__0();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__0);
l_Lake_DSL_dirConst___closed__1 = _init_l_Lake_DSL_dirConst___closed__1();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__1);
l_Lake_DSL_dirConst___closed__2 = _init_l_Lake_DSL_dirConst___closed__2();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__2);
l_Lake_DSL_dirConst___closed__3 = _init_l_Lake_DSL_dirConst___closed__3();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__3);
l_Lake_DSL_dirConst___closed__4 = _init_l_Lake_DSL_dirConst___closed__4();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__4);
l_Lake_DSL_dirConst___closed__5 = _init_l_Lake_DSL_dirConst___closed__5();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__5);
l_Lake_DSL_dirConst___closed__6 = _init_l_Lake_DSL_dirConst___closed__6();
lean_mark_persistent(l_Lake_DSL_dirConst___closed__6);
l_Lake_DSL_dirConst = _init_l_Lake_DSL_dirConst();
lean_mark_persistent(l_Lake_DSL_dirConst);
l_Lake_DSL_getConfig___closed__0 = _init_l_Lake_DSL_getConfig___closed__0();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__0);
l_Lake_DSL_getConfig___closed__1 = _init_l_Lake_DSL_getConfig___closed__1();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__1);
l_Lake_DSL_getConfig___closed__2 = _init_l_Lake_DSL_getConfig___closed__2();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__2);
l_Lake_DSL_getConfig___closed__3 = _init_l_Lake_DSL_getConfig___closed__3();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__3);
l_Lake_DSL_getConfig___closed__4 = _init_l_Lake_DSL_getConfig___closed__4();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__4);
l_Lake_DSL_getConfig___closed__5 = _init_l_Lake_DSL_getConfig___closed__5();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__5);
l_Lake_DSL_getConfig___closed__6 = _init_l_Lake_DSL_getConfig___closed__6();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__6);
l_Lake_DSL_getConfig___closed__7 = _init_l_Lake_DSL_getConfig___closed__7();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__7);
l_Lake_DSL_getConfig___closed__8 = _init_l_Lake_DSL_getConfig___closed__8();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__8);
l_Lake_DSL_getConfig___closed__9 = _init_l_Lake_DSL_getConfig___closed__9();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__9);
l_Lake_DSL_getConfig___closed__10 = _init_l_Lake_DSL_getConfig___closed__10();
lean_mark_persistent(l_Lake_DSL_getConfig___closed__10);
l_Lake_DSL_getConfig = _init_l_Lake_DSL_getConfig();
lean_mark_persistent(l_Lake_DSL_getConfig);
l_Lake_DSL_packageCommand___closed__0 = _init_l_Lake_DSL_packageCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__0);
l_Lake_DSL_packageCommand___closed__1 = _init_l_Lake_DSL_packageCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__1);
l_Lake_DSL_packageCommand___closed__2 = _init_l_Lake_DSL_packageCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__2);
l_Lake_DSL_packageCommand___closed__3 = _init_l_Lake_DSL_packageCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__3);
l_Lake_DSL_packageCommand___closed__4 = _init_l_Lake_DSL_packageCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__4);
l_Lake_DSL_packageCommand___closed__5 = _init_l_Lake_DSL_packageCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__5);
l_Lake_DSL_packageCommand___closed__6 = _init_l_Lake_DSL_packageCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__6);
l_Lake_DSL_packageCommand___closed__7 = _init_l_Lake_DSL_packageCommand___closed__7();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__7);
l_Lake_DSL_packageCommand___closed__8 = _init_l_Lake_DSL_packageCommand___closed__8();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__8);
l_Lake_DSL_packageCommand___closed__9 = _init_l_Lake_DSL_packageCommand___closed__9();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__9);
l_Lake_DSL_packageCommand___closed__10 = _init_l_Lake_DSL_packageCommand___closed__10();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__10);
l_Lake_DSL_packageCommand___closed__11 = _init_l_Lake_DSL_packageCommand___closed__11();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__11);
l_Lake_DSL_packageCommand___closed__12 = _init_l_Lake_DSL_packageCommand___closed__12();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__12);
l_Lake_DSL_packageCommand___closed__13 = _init_l_Lake_DSL_packageCommand___closed__13();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__13);
l_Lake_DSL_packageCommand___closed__14 = _init_l_Lake_DSL_packageCommand___closed__14();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__14);
l_Lake_DSL_packageCommand___closed__15 = _init_l_Lake_DSL_packageCommand___closed__15();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__15);
l_Lake_DSL_packageCommand___closed__16 = _init_l_Lake_DSL_packageCommand___closed__16();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__16);
l_Lake_DSL_packageCommand___closed__17 = _init_l_Lake_DSL_packageCommand___closed__17();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__17);
l_Lake_DSL_packageCommand___closed__18 = _init_l_Lake_DSL_packageCommand___closed__18();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__18);
l_Lake_DSL_packageCommand___closed__19 = _init_l_Lake_DSL_packageCommand___closed__19();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__19);
l_Lake_DSL_packageCommand___closed__20 = _init_l_Lake_DSL_packageCommand___closed__20();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__20);
l_Lake_DSL_packageCommand___closed__21 = _init_l_Lake_DSL_packageCommand___closed__21();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__21);
l_Lake_DSL_packageCommand___closed__22 = _init_l_Lake_DSL_packageCommand___closed__22();
lean_mark_persistent(l_Lake_DSL_packageCommand___closed__22);
l_Lake_DSL_packageCommand = _init_l_Lake_DSL_packageCommand();
lean_mark_persistent(l_Lake_DSL_packageCommand);
l_Lake_DSL_postUpdateDecl___closed__0 = _init_l_Lake_DSL_postUpdateDecl___closed__0();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__0);
l_Lake_DSL_postUpdateDecl___closed__1 = _init_l_Lake_DSL_postUpdateDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__1);
l_Lake_DSL_postUpdateDecl___closed__2 = _init_l_Lake_DSL_postUpdateDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__2);
l_Lake_DSL_postUpdateDecl___closed__3 = _init_l_Lake_DSL_postUpdateDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__3);
l_Lake_DSL_postUpdateDecl___closed__4 = _init_l_Lake_DSL_postUpdateDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__4);
l_Lake_DSL_postUpdateDecl___closed__5 = _init_l_Lake_DSL_postUpdateDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__5);
l_Lake_DSL_postUpdateDecl___closed__6 = _init_l_Lake_DSL_postUpdateDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__6);
l_Lake_DSL_postUpdateDecl___closed__7 = _init_l_Lake_DSL_postUpdateDecl___closed__7();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__7);
l_Lake_DSL_postUpdateDecl___closed__8 = _init_l_Lake_DSL_postUpdateDecl___closed__8();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__8);
l_Lake_DSL_postUpdateDecl___closed__9 = _init_l_Lake_DSL_postUpdateDecl___closed__9();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__9);
l_Lake_DSL_postUpdateDecl___closed__10 = _init_l_Lake_DSL_postUpdateDecl___closed__10();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__10);
l_Lake_DSL_postUpdateDecl___closed__11 = _init_l_Lake_DSL_postUpdateDecl___closed__11();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__11);
l_Lake_DSL_postUpdateDecl___closed__12 = _init_l_Lake_DSL_postUpdateDecl___closed__12();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__12);
l_Lake_DSL_postUpdateDecl___closed__13 = _init_l_Lake_DSL_postUpdateDecl___closed__13();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__13);
l_Lake_DSL_postUpdateDecl___closed__14 = _init_l_Lake_DSL_postUpdateDecl___closed__14();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__14);
l_Lake_DSL_postUpdateDecl___closed__15 = _init_l_Lake_DSL_postUpdateDecl___closed__15();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__15);
l_Lake_DSL_postUpdateDecl___closed__16 = _init_l_Lake_DSL_postUpdateDecl___closed__16();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__16);
l_Lake_DSL_postUpdateDecl___closed__17 = _init_l_Lake_DSL_postUpdateDecl___closed__17();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__17);
l_Lake_DSL_postUpdateDecl___closed__18 = _init_l_Lake_DSL_postUpdateDecl___closed__18();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__18);
l_Lake_DSL_postUpdateDecl___closed__19 = _init_l_Lake_DSL_postUpdateDecl___closed__19();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl___closed__19);
l_Lake_DSL_postUpdateDecl = _init_l_Lake_DSL_postUpdateDecl();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl);
l_Lake_DSL_fromPath___closed__0 = _init_l_Lake_DSL_fromPath___closed__0();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__0);
l_Lake_DSL_fromPath___closed__1 = _init_l_Lake_DSL_fromPath___closed__1();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__1);
l_Lake_DSL_fromPath___closed__2 = _init_l_Lake_DSL_fromPath___closed__2();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__2);
l_Lake_DSL_fromPath___closed__3 = _init_l_Lake_DSL_fromPath___closed__3();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__3);
l_Lake_DSL_fromPath___closed__4 = _init_l_Lake_DSL_fromPath___closed__4();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__4);
l_Lake_DSL_fromPath___closed__5 = _init_l_Lake_DSL_fromPath___closed__5();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__5);
l_Lake_DSL_fromPath = _init_l_Lake_DSL_fromPath();
lean_mark_persistent(l_Lake_DSL_fromPath);
l_Lake_DSL_fromGit___closed__0 = _init_l_Lake_DSL_fromGit___closed__0();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__0);
l_Lake_DSL_fromGit___closed__1 = _init_l_Lake_DSL_fromGit___closed__1();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__1);
l_Lake_DSL_fromGit___closed__2 = _init_l_Lake_DSL_fromGit___closed__2();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__2);
l_Lake_DSL_fromGit___closed__3 = _init_l_Lake_DSL_fromGit___closed__3();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__3);
l_Lake_DSL_fromGit___closed__4 = _init_l_Lake_DSL_fromGit___closed__4();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__4);
l_Lake_DSL_fromGit___closed__5 = _init_l_Lake_DSL_fromGit___closed__5();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__5);
l_Lake_DSL_fromGit___closed__6 = _init_l_Lake_DSL_fromGit___closed__6();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__6);
l_Lake_DSL_fromGit___closed__7 = _init_l_Lake_DSL_fromGit___closed__7();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__7);
l_Lake_DSL_fromGit___closed__8 = _init_l_Lake_DSL_fromGit___closed__8();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__8);
l_Lake_DSL_fromGit___closed__9 = _init_l_Lake_DSL_fromGit___closed__9();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__9);
l_Lake_DSL_fromGit___closed__10 = _init_l_Lake_DSL_fromGit___closed__10();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__10);
l_Lake_DSL_fromGit___closed__11 = _init_l_Lake_DSL_fromGit___closed__11();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__11);
l_Lake_DSL_fromGit___closed__12 = _init_l_Lake_DSL_fromGit___closed__12();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__12);
l_Lake_DSL_fromGit___closed__13 = _init_l_Lake_DSL_fromGit___closed__13();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__13);
l_Lake_DSL_fromGit___closed__14 = _init_l_Lake_DSL_fromGit___closed__14();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__14);
l_Lake_DSL_fromGit___closed__15 = _init_l_Lake_DSL_fromGit___closed__15();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__15);
l_Lake_DSL_fromGit___closed__16 = _init_l_Lake_DSL_fromGit___closed__16();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__16);
l_Lake_DSL_fromGit = _init_l_Lake_DSL_fromGit();
lean_mark_persistent(l_Lake_DSL_fromGit);
l_Lake_DSL_fromSource___closed__0 = _init_l_Lake_DSL_fromSource___closed__0();
lean_mark_persistent(l_Lake_DSL_fromSource___closed__0);
l_Lake_DSL_fromSource___closed__1 = _init_l_Lake_DSL_fromSource___closed__1();
lean_mark_persistent(l_Lake_DSL_fromSource___closed__1);
l_Lake_DSL_fromSource___closed__2 = _init_l_Lake_DSL_fromSource___closed__2();
lean_mark_persistent(l_Lake_DSL_fromSource___closed__2);
l_Lake_DSL_fromSource___closed__3 = _init_l_Lake_DSL_fromSource___closed__3();
lean_mark_persistent(l_Lake_DSL_fromSource___closed__3);
l_Lake_DSL_fromSource = _init_l_Lake_DSL_fromSource();
lean_mark_persistent(l_Lake_DSL_fromSource);
l_Lake_DSL_fromClause___closed__0 = _init_l_Lake_DSL_fromClause___closed__0();
lean_mark_persistent(l_Lake_DSL_fromClause___closed__0);
l_Lake_DSL_fromClause___closed__1 = _init_l_Lake_DSL_fromClause___closed__1();
lean_mark_persistent(l_Lake_DSL_fromClause___closed__1);
l_Lake_DSL_fromClause___closed__2 = _init_l_Lake_DSL_fromClause___closed__2();
lean_mark_persistent(l_Lake_DSL_fromClause___closed__2);
l_Lake_DSL_fromClause___closed__3 = _init_l_Lake_DSL_fromClause___closed__3();
lean_mark_persistent(l_Lake_DSL_fromClause___closed__3);
l_Lake_DSL_fromClause___closed__4 = _init_l_Lake_DSL_fromClause___closed__4();
lean_mark_persistent(l_Lake_DSL_fromClause___closed__4);
l_Lake_DSL_fromClause___closed__5 = _init_l_Lake_DSL_fromClause___closed__5();
lean_mark_persistent(l_Lake_DSL_fromClause___closed__5);
l_Lake_DSL_fromClause = _init_l_Lake_DSL_fromClause();
lean_mark_persistent(l_Lake_DSL_fromClause);
l_Lake_DSL_withClause___closed__0 = _init_l_Lake_DSL_withClause___closed__0();
lean_mark_persistent(l_Lake_DSL_withClause___closed__0);
l_Lake_DSL_withClause___closed__1 = _init_l_Lake_DSL_withClause___closed__1();
lean_mark_persistent(l_Lake_DSL_withClause___closed__1);
l_Lake_DSL_withClause___closed__2 = _init_l_Lake_DSL_withClause___closed__2();
lean_mark_persistent(l_Lake_DSL_withClause___closed__2);
l_Lake_DSL_withClause___closed__3 = _init_l_Lake_DSL_withClause___closed__3();
lean_mark_persistent(l_Lake_DSL_withClause___closed__3);
l_Lake_DSL_withClause___closed__4 = _init_l_Lake_DSL_withClause___closed__4();
lean_mark_persistent(l_Lake_DSL_withClause___closed__4);
l_Lake_DSL_withClause___closed__5 = _init_l_Lake_DSL_withClause___closed__5();
lean_mark_persistent(l_Lake_DSL_withClause___closed__5);
l_Lake_DSL_withClause = _init_l_Lake_DSL_withClause();
lean_mark_persistent(l_Lake_DSL_withClause);
l_Lake_DSL_verSpec___closed__0 = _init_l_Lake_DSL_verSpec___closed__0();
lean_mark_persistent(l_Lake_DSL_verSpec___closed__0);
l_Lake_DSL_verSpec___closed__1 = _init_l_Lake_DSL_verSpec___closed__1();
lean_mark_persistent(l_Lake_DSL_verSpec___closed__1);
l_Lake_DSL_verSpec___closed__2 = _init_l_Lake_DSL_verSpec___closed__2();
lean_mark_persistent(l_Lake_DSL_verSpec___closed__2);
l_Lake_DSL_verSpec___closed__3 = _init_l_Lake_DSL_verSpec___closed__3();
lean_mark_persistent(l_Lake_DSL_verSpec___closed__3);
l_Lake_DSL_verSpec___closed__4 = _init_l_Lake_DSL_verSpec___closed__4();
lean_mark_persistent(l_Lake_DSL_verSpec___closed__4);
l_Lake_DSL_verSpec = _init_l_Lake_DSL_verSpec();
lean_mark_persistent(l_Lake_DSL_verSpec);
l_Lake_DSL_verClause___closed__0 = _init_l_Lake_DSL_verClause___closed__0();
lean_mark_persistent(l_Lake_DSL_verClause___closed__0);
l_Lake_DSL_verClause___closed__1 = _init_l_Lake_DSL_verClause___closed__1();
lean_mark_persistent(l_Lake_DSL_verClause___closed__1);
l_Lake_DSL_verClause___closed__2 = _init_l_Lake_DSL_verClause___closed__2();
lean_mark_persistent(l_Lake_DSL_verClause___closed__2);
l_Lake_DSL_verClause___closed__3 = _init_l_Lake_DSL_verClause___closed__3();
lean_mark_persistent(l_Lake_DSL_verClause___closed__3);
l_Lake_DSL_verClause___closed__4 = _init_l_Lake_DSL_verClause___closed__4();
lean_mark_persistent(l_Lake_DSL_verClause___closed__4);
l_Lake_DSL_verClause___closed__5 = _init_l_Lake_DSL_verClause___closed__5();
lean_mark_persistent(l_Lake_DSL_verClause___closed__5);
l_Lake_DSL_verClause = _init_l_Lake_DSL_verClause();
lean_mark_persistent(l_Lake_DSL_verClause);
l_Lake_DSL_depName___closed__0 = _init_l_Lake_DSL_depName___closed__0();
lean_mark_persistent(l_Lake_DSL_depName___closed__0);
l_Lake_DSL_depName___closed__1 = _init_l_Lake_DSL_depName___closed__1();
lean_mark_persistent(l_Lake_DSL_depName___closed__1);
l_Lake_DSL_depName___closed__2 = _init_l_Lake_DSL_depName___closed__2();
lean_mark_persistent(l_Lake_DSL_depName___closed__2);
l_Lake_DSL_depName___closed__3 = _init_l_Lake_DSL_depName___closed__3();
lean_mark_persistent(l_Lake_DSL_depName___closed__3);
l_Lake_DSL_depName___closed__4 = _init_l_Lake_DSL_depName___closed__4();
lean_mark_persistent(l_Lake_DSL_depName___closed__4);
l_Lake_DSL_depName___closed__5 = _init_l_Lake_DSL_depName___closed__5();
lean_mark_persistent(l_Lake_DSL_depName___closed__5);
l_Lake_DSL_depName___closed__6 = _init_l_Lake_DSL_depName___closed__6();
lean_mark_persistent(l_Lake_DSL_depName___closed__6);
l_Lake_DSL_depName___closed__7 = _init_l_Lake_DSL_depName___closed__7();
lean_mark_persistent(l_Lake_DSL_depName___closed__7);
l_Lake_DSL_depName___closed__8 = _init_l_Lake_DSL_depName___closed__8();
lean_mark_persistent(l_Lake_DSL_depName___closed__8);
l_Lake_DSL_depName___closed__9 = _init_l_Lake_DSL_depName___closed__9();
lean_mark_persistent(l_Lake_DSL_depName___closed__9);
l_Lake_DSL_depName___closed__10 = _init_l_Lake_DSL_depName___closed__10();
lean_mark_persistent(l_Lake_DSL_depName___closed__10);
l_Lake_DSL_depName___closed__11 = _init_l_Lake_DSL_depName___closed__11();
lean_mark_persistent(l_Lake_DSL_depName___closed__11);
l_Lake_DSL_depName___closed__12 = _init_l_Lake_DSL_depName___closed__12();
lean_mark_persistent(l_Lake_DSL_depName___closed__12);
l_Lake_DSL_depName___closed__13 = _init_l_Lake_DSL_depName___closed__13();
lean_mark_persistent(l_Lake_DSL_depName___closed__13);
l_Lake_DSL_depName = _init_l_Lake_DSL_depName();
lean_mark_persistent(l_Lake_DSL_depName);
l_Lake_DSL_depSpec___closed__0 = _init_l_Lake_DSL_depSpec___closed__0();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__0);
l_Lake_DSL_depSpec___closed__1 = _init_l_Lake_DSL_depSpec___closed__1();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__1);
l_Lake_DSL_depSpec___closed__2 = _init_l_Lake_DSL_depSpec___closed__2();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__2);
l_Lake_DSL_depSpec___closed__3 = _init_l_Lake_DSL_depSpec___closed__3();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__3);
l_Lake_DSL_depSpec___closed__4 = _init_l_Lake_DSL_depSpec___closed__4();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__4);
l_Lake_DSL_depSpec___closed__5 = _init_l_Lake_DSL_depSpec___closed__5();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__5);
l_Lake_DSL_depSpec___closed__6 = _init_l_Lake_DSL_depSpec___closed__6();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__6);
l_Lake_DSL_depSpec___closed__7 = _init_l_Lake_DSL_depSpec___closed__7();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__7);
l_Lake_DSL_depSpec___closed__8 = _init_l_Lake_DSL_depSpec___closed__8();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__8);
l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
lean_mark_persistent(l_Lake_DSL_depSpec);
l_Lake_DSL_requireDecl___closed__0 = _init_l_Lake_DSL_requireDecl___closed__0();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__0);
l_Lake_DSL_requireDecl___closed__1 = _init_l_Lake_DSL_requireDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__1);
l_Lake_DSL_requireDecl___closed__2 = _init_l_Lake_DSL_requireDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__2);
l_Lake_DSL_requireDecl___closed__3 = _init_l_Lake_DSL_requireDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__3);
l_Lake_DSL_requireDecl___closed__4 = _init_l_Lake_DSL_requireDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__4);
l_Lake_DSL_requireDecl___closed__5 = _init_l_Lake_DSL_requireDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__5);
l_Lake_DSL_requireDecl___closed__6 = _init_l_Lake_DSL_requireDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__6);
l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
lean_mark_persistent(l_Lake_DSL_requireDecl);
l_Lake_DSL_buildDeclSig___closed__0 = _init_l_Lake_DSL_buildDeclSig___closed__0();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__0);
l_Lake_DSL_buildDeclSig___closed__1 = _init_l_Lake_DSL_buildDeclSig___closed__1();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__1);
l_Lake_DSL_buildDeclSig___closed__2 = _init_l_Lake_DSL_buildDeclSig___closed__2();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__2);
l_Lake_DSL_buildDeclSig___closed__3 = _init_l_Lake_DSL_buildDeclSig___closed__3();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__3);
l_Lake_DSL_buildDeclSig___closed__4 = _init_l_Lake_DSL_buildDeclSig___closed__4();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__4);
l_Lake_DSL_buildDeclSig___closed__5 = _init_l_Lake_DSL_buildDeclSig___closed__5();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__5);
l_Lake_DSL_buildDeclSig___closed__6 = _init_l_Lake_DSL_buildDeclSig___closed__6();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__6);
l_Lake_DSL_buildDeclSig___closed__7 = _init_l_Lake_DSL_buildDeclSig___closed__7();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__7);
l_Lake_DSL_buildDeclSig___closed__8 = _init_l_Lake_DSL_buildDeclSig___closed__8();
lean_mark_persistent(l_Lake_DSL_buildDeclSig___closed__8);
l_Lake_DSL_buildDeclSig = _init_l_Lake_DSL_buildDeclSig();
lean_mark_persistent(l_Lake_DSL_buildDeclSig);
l_Lake_DSL_moduleFacetDecl___closed__0 = _init_l_Lake_DSL_moduleFacetDecl___closed__0();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__0);
l_Lake_DSL_moduleFacetDecl___closed__1 = _init_l_Lake_DSL_moduleFacetDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__1);
l_Lake_DSL_moduleFacetDecl___closed__2 = _init_l_Lake_DSL_moduleFacetDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__2);
l_Lake_DSL_moduleFacetDecl___closed__3 = _init_l_Lake_DSL_moduleFacetDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__3);
l_Lake_DSL_moduleFacetDecl___closed__4 = _init_l_Lake_DSL_moduleFacetDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__4);
l_Lake_DSL_moduleFacetDecl___closed__5 = _init_l_Lake_DSL_moduleFacetDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__5);
l_Lake_DSL_moduleFacetDecl___closed__6 = _init_l_Lake_DSL_moduleFacetDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl___closed__6);
l_Lake_DSL_moduleFacetDecl = _init_l_Lake_DSL_moduleFacetDecl();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl);
l_Lake_DSL_packageFacetDecl___closed__0 = _init_l_Lake_DSL_packageFacetDecl___closed__0();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__0);
l_Lake_DSL_packageFacetDecl___closed__1 = _init_l_Lake_DSL_packageFacetDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__1);
l_Lake_DSL_packageFacetDecl___closed__2 = _init_l_Lake_DSL_packageFacetDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__2);
l_Lake_DSL_packageFacetDecl___closed__3 = _init_l_Lake_DSL_packageFacetDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__3);
l_Lake_DSL_packageFacetDecl___closed__4 = _init_l_Lake_DSL_packageFacetDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__4);
l_Lake_DSL_packageFacetDecl___closed__5 = _init_l_Lake_DSL_packageFacetDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__5);
l_Lake_DSL_packageFacetDecl___closed__6 = _init_l_Lake_DSL_packageFacetDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl___closed__6);
l_Lake_DSL_packageFacetDecl = _init_l_Lake_DSL_packageFacetDecl();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl);
l_Lake_DSL_libraryFacetDecl___closed__0 = _init_l_Lake_DSL_libraryFacetDecl___closed__0();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__0);
l_Lake_DSL_libraryFacetDecl___closed__1 = _init_l_Lake_DSL_libraryFacetDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__1);
l_Lake_DSL_libraryFacetDecl___closed__2 = _init_l_Lake_DSL_libraryFacetDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__2);
l_Lake_DSL_libraryFacetDecl___closed__3 = _init_l_Lake_DSL_libraryFacetDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__3);
l_Lake_DSL_libraryFacetDecl___closed__4 = _init_l_Lake_DSL_libraryFacetDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__4);
l_Lake_DSL_libraryFacetDecl___closed__5 = _init_l_Lake_DSL_libraryFacetDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__5);
l_Lake_DSL_libraryFacetDecl___closed__6 = _init_l_Lake_DSL_libraryFacetDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl___closed__6);
l_Lake_DSL_libraryFacetDecl = _init_l_Lake_DSL_libraryFacetDecl();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl);
l_Lake_DSL_targetCommand___closed__0 = _init_l_Lake_DSL_targetCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__0);
l_Lake_DSL_targetCommand___closed__1 = _init_l_Lake_DSL_targetCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__1);
l_Lake_DSL_targetCommand___closed__2 = _init_l_Lake_DSL_targetCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__2);
l_Lake_DSL_targetCommand___closed__3 = _init_l_Lake_DSL_targetCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__3);
l_Lake_DSL_targetCommand___closed__4 = _init_l_Lake_DSL_targetCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__4);
l_Lake_DSL_targetCommand___closed__5 = _init_l_Lake_DSL_targetCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__5);
l_Lake_DSL_targetCommand___closed__6 = _init_l_Lake_DSL_targetCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_targetCommand___closed__6);
l_Lake_DSL_targetCommand = _init_l_Lake_DSL_targetCommand();
lean_mark_persistent(l_Lake_DSL_targetCommand);
l_Lake_DSL_leanLibCommand___closed__0 = _init_l_Lake_DSL_leanLibCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__0);
l_Lake_DSL_leanLibCommand___closed__1 = _init_l_Lake_DSL_leanLibCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__1);
l_Lake_DSL_leanLibCommand___closed__2 = _init_l_Lake_DSL_leanLibCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__2);
l_Lake_DSL_leanLibCommand___closed__3 = _init_l_Lake_DSL_leanLibCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__3);
l_Lake_DSL_leanLibCommand___closed__4 = _init_l_Lake_DSL_leanLibCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__4);
l_Lake_DSL_leanLibCommand___closed__5 = _init_l_Lake_DSL_leanLibCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__5);
l_Lake_DSL_leanLibCommand___closed__6 = _init_l_Lake_DSL_leanLibCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__6);
l_Lake_DSL_leanLibCommand___closed__7 = _init_l_Lake_DSL_leanLibCommand___closed__7();
lean_mark_persistent(l_Lake_DSL_leanLibCommand___closed__7);
l_Lake_DSL_leanLibCommand = _init_l_Lake_DSL_leanLibCommand();
lean_mark_persistent(l_Lake_DSL_leanLibCommand);
l_Lake_DSL_leanExeCommand___closed__0 = _init_l_Lake_DSL_leanExeCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__0);
l_Lake_DSL_leanExeCommand___closed__1 = _init_l_Lake_DSL_leanExeCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__1);
l_Lake_DSL_leanExeCommand___closed__2 = _init_l_Lake_DSL_leanExeCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__2);
l_Lake_DSL_leanExeCommand___closed__3 = _init_l_Lake_DSL_leanExeCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__3);
l_Lake_DSL_leanExeCommand___closed__4 = _init_l_Lake_DSL_leanExeCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__4);
l_Lake_DSL_leanExeCommand___closed__5 = _init_l_Lake_DSL_leanExeCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__5);
l_Lake_DSL_leanExeCommand___closed__6 = _init_l_Lake_DSL_leanExeCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__6);
l_Lake_DSL_leanExeCommand___closed__7 = _init_l_Lake_DSL_leanExeCommand___closed__7();
lean_mark_persistent(l_Lake_DSL_leanExeCommand___closed__7);
l_Lake_DSL_leanExeCommand = _init_l_Lake_DSL_leanExeCommand();
lean_mark_persistent(l_Lake_DSL_leanExeCommand);
l_Lake_DSL_inputFileCommand___closed__0 = _init_l_Lake_DSL_inputFileCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__0);
l_Lake_DSL_inputFileCommand___closed__1 = _init_l_Lake_DSL_inputFileCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__1);
l_Lake_DSL_inputFileCommand___closed__2 = _init_l_Lake_DSL_inputFileCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__2);
l_Lake_DSL_inputFileCommand___closed__3 = _init_l_Lake_DSL_inputFileCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__3);
l_Lake_DSL_inputFileCommand___closed__4 = _init_l_Lake_DSL_inputFileCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__4);
l_Lake_DSL_inputFileCommand___closed__5 = _init_l_Lake_DSL_inputFileCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__5);
l_Lake_DSL_inputFileCommand___closed__6 = _init_l_Lake_DSL_inputFileCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__6);
l_Lake_DSL_inputFileCommand___closed__7 = _init_l_Lake_DSL_inputFileCommand___closed__7();
lean_mark_persistent(l_Lake_DSL_inputFileCommand___closed__7);
l_Lake_DSL_inputFileCommand = _init_l_Lake_DSL_inputFileCommand();
lean_mark_persistent(l_Lake_DSL_inputFileCommand);
l_Lake_DSL_inputDirCommand___closed__0 = _init_l_Lake_DSL_inputDirCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__0);
l_Lake_DSL_inputDirCommand___closed__1 = _init_l_Lake_DSL_inputDirCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__1);
l_Lake_DSL_inputDirCommand___closed__2 = _init_l_Lake_DSL_inputDirCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__2);
l_Lake_DSL_inputDirCommand___closed__3 = _init_l_Lake_DSL_inputDirCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__3);
l_Lake_DSL_inputDirCommand___closed__4 = _init_l_Lake_DSL_inputDirCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__4);
l_Lake_DSL_inputDirCommand___closed__5 = _init_l_Lake_DSL_inputDirCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__5);
l_Lake_DSL_inputDirCommand___closed__6 = _init_l_Lake_DSL_inputDirCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__6);
l_Lake_DSL_inputDirCommand___closed__7 = _init_l_Lake_DSL_inputDirCommand___closed__7();
lean_mark_persistent(l_Lake_DSL_inputDirCommand___closed__7);
l_Lake_DSL_inputDirCommand = _init_l_Lake_DSL_inputDirCommand();
lean_mark_persistent(l_Lake_DSL_inputDirCommand);
l_Lake_DSL_externLibDeclSpec___closed__0 = _init_l_Lake_DSL_externLibDeclSpec___closed__0();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec___closed__0);
l_Lake_DSL_externLibDeclSpec___closed__1 = _init_l_Lake_DSL_externLibDeclSpec___closed__1();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec___closed__1);
l_Lake_DSL_externLibDeclSpec___closed__2 = _init_l_Lake_DSL_externLibDeclSpec___closed__2();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec___closed__2);
l_Lake_DSL_externLibDeclSpec___closed__3 = _init_l_Lake_DSL_externLibDeclSpec___closed__3();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec___closed__3);
l_Lake_DSL_externLibDeclSpec = _init_l_Lake_DSL_externLibDeclSpec();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec);
l_Lake_DSL_externLibCommand___closed__0 = _init_l_Lake_DSL_externLibCommand___closed__0();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__0);
l_Lake_DSL_externLibCommand___closed__1 = _init_l_Lake_DSL_externLibCommand___closed__1();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__1);
l_Lake_DSL_externLibCommand___closed__2 = _init_l_Lake_DSL_externLibCommand___closed__2();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__2);
l_Lake_DSL_externLibCommand___closed__3 = _init_l_Lake_DSL_externLibCommand___closed__3();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__3);
l_Lake_DSL_externLibCommand___closed__4 = _init_l_Lake_DSL_externLibCommand___closed__4();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__4);
l_Lake_DSL_externLibCommand___closed__5 = _init_l_Lake_DSL_externLibCommand___closed__5();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__5);
l_Lake_DSL_externLibCommand___closed__6 = _init_l_Lake_DSL_externLibCommand___closed__6();
lean_mark_persistent(l_Lake_DSL_externLibCommand___closed__6);
l_Lake_DSL_externLibCommand = _init_l_Lake_DSL_externLibCommand();
lean_mark_persistent(l_Lake_DSL_externLibCommand);
l_Lake_DSL_scriptDeclSpec___closed__0 = _init_l_Lake_DSL_scriptDeclSpec___closed__0();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec___closed__0);
l_Lake_DSL_scriptDeclSpec___closed__1 = _init_l_Lake_DSL_scriptDeclSpec___closed__1();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec___closed__1);
l_Lake_DSL_scriptDeclSpec___closed__2 = _init_l_Lake_DSL_scriptDeclSpec___closed__2();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec___closed__2);
l_Lake_DSL_scriptDeclSpec___closed__3 = _init_l_Lake_DSL_scriptDeclSpec___closed__3();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec___closed__3);
l_Lake_DSL_scriptDeclSpec = _init_l_Lake_DSL_scriptDeclSpec();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec);
l_Lake_DSL_scriptDecl___closed__0 = _init_l_Lake_DSL_scriptDecl___closed__0();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__0);
l_Lake_DSL_scriptDecl___closed__1 = _init_l_Lake_DSL_scriptDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__1);
l_Lake_DSL_scriptDecl___closed__2 = _init_l_Lake_DSL_scriptDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__2);
l_Lake_DSL_scriptDecl___closed__3 = _init_l_Lake_DSL_scriptDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__3);
l_Lake_DSL_scriptDecl___closed__4 = _init_l_Lake_DSL_scriptDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__4);
l_Lake_DSL_scriptDecl___closed__5 = _init_l_Lake_DSL_scriptDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__5);
l_Lake_DSL_scriptDecl___closed__6 = _init_l_Lake_DSL_scriptDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_scriptDecl___closed__6);
l_Lake_DSL_scriptDecl = _init_l_Lake_DSL_scriptDecl();
lean_mark_persistent(l_Lake_DSL_scriptDecl);
l_Lake_verLit___closed__0 = _init_l_Lake_verLit___closed__0();
lean_mark_persistent(l_Lake_verLit___closed__0);
l_Lake_verLit___closed__1 = _init_l_Lake_verLit___closed__1();
lean_mark_persistent(l_Lake_verLit___closed__1);
l_Lake_verLit___closed__2 = _init_l_Lake_verLit___closed__2();
lean_mark_persistent(l_Lake_verLit___closed__2);
l_Lake_verLit___closed__3 = _init_l_Lake_verLit___closed__3();
lean_mark_persistent(l_Lake_verLit___closed__3);
l_Lake_verLit___closed__4 = _init_l_Lake_verLit___closed__4();
lean_mark_persistent(l_Lake_verLit___closed__4);
l_Lake_verLit___closed__5 = _init_l_Lake_verLit___closed__5();
lean_mark_persistent(l_Lake_verLit___closed__5);
l_Lake_verLit___closed__6 = _init_l_Lake_verLit___closed__6();
lean_mark_persistent(l_Lake_verLit___closed__6);
l_Lake_verLit___closed__7 = _init_l_Lake_verLit___closed__7();
lean_mark_persistent(l_Lake_verLit___closed__7);
l_Lake_verLit___closed__8 = _init_l_Lake_verLit___closed__8();
lean_mark_persistent(l_Lake_verLit___closed__8);
l_Lake_verLit___closed__9 = _init_l_Lake_verLit___closed__9();
lean_mark_persistent(l_Lake_verLit___closed__9);
l_Lake_verLit___closed__10 = _init_l_Lake_verLit___closed__10();
lean_mark_persistent(l_Lake_verLit___closed__10);
l_Lake_verLit___closed__11 = _init_l_Lake_verLit___closed__11();
lean_mark_persistent(l_Lake_verLit___closed__11);
l_Lake_verLit___closed__12 = _init_l_Lake_verLit___closed__12();
lean_mark_persistent(l_Lake_verLit___closed__12);
l_Lake_verLit = _init_l_Lake_verLit();
lean_mark_persistent(l_Lake_verLit);
l_Lake_DSL_facetSuffix___closed__0 = _init_l_Lake_DSL_facetSuffix___closed__0();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__0);
l_Lake_DSL_facetSuffix___closed__1 = _init_l_Lake_DSL_facetSuffix___closed__1();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__1);
l_Lake_DSL_facetSuffix___closed__2 = _init_l_Lake_DSL_facetSuffix___closed__2();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__2);
l_Lake_DSL_facetSuffix___closed__3 = _init_l_Lake_DSL_facetSuffix___closed__3();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__3);
l_Lake_DSL_facetSuffix___closed__4 = _init_l_Lake_DSL_facetSuffix___closed__4();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__4);
l_Lake_DSL_facetSuffix___closed__5 = _init_l_Lake_DSL_facetSuffix___closed__5();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__5);
l_Lake_DSL_facetSuffix___closed__6 = _init_l_Lake_DSL_facetSuffix___closed__6();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__6);
l_Lake_DSL_facetSuffix___closed__7 = _init_l_Lake_DSL_facetSuffix___closed__7();
lean_mark_persistent(l_Lake_DSL_facetSuffix___closed__7);
l_Lake_DSL_facetSuffix = _init_l_Lake_DSL_facetSuffix();
lean_mark_persistent(l_Lake_DSL_facetSuffix);
l_Lake_DSL_packageTargetLit___closed__0 = _init_l_Lake_DSL_packageTargetLit___closed__0();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__0);
l_Lake_DSL_packageTargetLit___closed__1 = _init_l_Lake_DSL_packageTargetLit___closed__1();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__1);
l_Lake_DSL_packageTargetLit___closed__2 = _init_l_Lake_DSL_packageTargetLit___closed__2();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__2);
l_Lake_DSL_packageTargetLit___closed__3 = _init_l_Lake_DSL_packageTargetLit___closed__3();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__3);
l_Lake_DSL_packageTargetLit___closed__4 = _init_l_Lake_DSL_packageTargetLit___closed__4();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__4);
l_Lake_DSL_packageTargetLit___closed__5 = _init_l_Lake_DSL_packageTargetLit___closed__5();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__5);
l_Lake_DSL_packageTargetLit___closed__6 = _init_l_Lake_DSL_packageTargetLit___closed__6();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__6);
l_Lake_DSL_packageTargetLit___closed__7 = _init_l_Lake_DSL_packageTargetLit___closed__7();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__7);
l_Lake_DSL_packageTargetLit___closed__8 = _init_l_Lake_DSL_packageTargetLit___closed__8();
lean_mark_persistent(l_Lake_DSL_packageTargetLit___closed__8);
l_Lake_DSL_packageTargetLit = _init_l_Lake_DSL_packageTargetLit();
lean_mark_persistent(l_Lake_DSL_packageTargetLit);
l_Lake_DSL_term_x60_x2b_________closed__0 = _init_l_Lake_DSL_term_x60_x2b_________closed__0();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__0);
l_Lake_DSL_term_x60_x2b_________closed__1 = _init_l_Lake_DSL_term_x60_x2b_________closed__1();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__1);
l_Lake_DSL_term_x60_x2b_________closed__2 = _init_l_Lake_DSL_term_x60_x2b_________closed__2();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__2);
l_Lake_DSL_term_x60_x2b_________closed__3 = _init_l_Lake_DSL_term_x60_x2b_________closed__3();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__3);
l_Lake_DSL_term_x60_x2b_________closed__4 = _init_l_Lake_DSL_term_x60_x2b_________closed__4();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__4);
l_Lake_DSL_term_x60_x2b_________closed__5 = _init_l_Lake_DSL_term_x60_x2b_________closed__5();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__5);
l_Lake_DSL_term_x60_x2b_________closed__6 = _init_l_Lake_DSL_term_x60_x2b_________closed__6();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__6);
l_Lake_DSL_term_x60_x2b_________closed__7 = _init_l_Lake_DSL_term_x60_x2b_________closed__7();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__7);
l_Lake_DSL_term_x60_x2b_________closed__8 = _init_l_Lake_DSL_term_x60_x2b_________closed__8();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__8);
l_Lake_DSL_term_x60_x2b_________closed__9 = _init_l_Lake_DSL_term_x60_x2b_________closed__9();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__9);
l_Lake_DSL_term_x60_x2b_________closed__10 = _init_l_Lake_DSL_term_x60_x2b_________closed__10();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b_________closed__10);
l_Lake_DSL_term_x60_x2b______ = _init_l_Lake_DSL_term_x60_x2b______();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b______);
l_Lake_DSL_term_x60_x40_______x2f___________closed__0 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__0();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__0);
l_Lake_DSL_term_x60_x40_______x2f___________closed__1 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__1();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__1);
l_Lake_DSL_term_x60_x40_______x2f___________closed__2 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__2();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__2);
l_Lake_DSL_term_x60_x40_______x2f___________closed__3 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__3();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__3);
l_Lake_DSL_term_x60_x40_______x2f___________closed__4 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__4();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__4);
l_Lake_DSL_term_x60_x40_______x2f___________closed__5 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__5();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__5);
l_Lake_DSL_term_x60_x40_______x2f___________closed__6 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__6();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__6);
l_Lake_DSL_term_x60_x40_______x2f___________closed__7 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__7();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__7);
l_Lake_DSL_term_x60_x40_______x2f___________closed__8 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__8();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__8);
l_Lake_DSL_term_x60_x40_______x2f___________closed__9 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__9();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__9);
l_Lake_DSL_term_x60_x40_______x2f___________closed__10 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__10();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__10);
l_Lake_DSL_term_x60_x40_______x2f___________closed__11 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__11();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__11);
l_Lake_DSL_term_x60_x40_______x2f___________closed__12 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__12();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__12);
l_Lake_DSL_term_x60_x40_______x2f___________closed__13 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__13();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__13);
l_Lake_DSL_term_x60_x40_______x2f___________closed__14 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__14();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__14);
l_Lake_DSL_term_x60_x40_______x2f___________closed__15 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__15();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__15);
l_Lake_DSL_term_x60_x40_______x2f___________closed__16 = _init_l_Lake_DSL_term_x60_x40_______x2f___________closed__16();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f___________closed__16);
l_Lake_DSL_term_x60_x40_______x2f________ = _init_l_Lake_DSL_term_x60_x40_______x2f________();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f________);
l_Lake_DSL_cmdDo___closed__0 = _init_l_Lake_DSL_cmdDo___closed__0();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__0);
l_Lake_DSL_cmdDo___closed__1 = _init_l_Lake_DSL_cmdDo___closed__1();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__1);
l_Lake_DSL_cmdDo___closed__2 = _init_l_Lake_DSL_cmdDo___closed__2();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__2);
l_Lake_DSL_cmdDo___closed__3 = _init_l_Lake_DSL_cmdDo___closed__3();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__3);
l_Lake_DSL_cmdDo___closed__4 = _init_l_Lake_DSL_cmdDo___closed__4();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__4);
l_Lake_DSL_cmdDo___closed__5 = _init_l_Lake_DSL_cmdDo___closed__5();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__5);
l_Lake_DSL_cmdDo___closed__6 = _init_l_Lake_DSL_cmdDo___closed__6();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__6);
l_Lake_DSL_cmdDo___closed__7 = _init_l_Lake_DSL_cmdDo___closed__7();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__7);
l_Lake_DSL_cmdDo___closed__8 = _init_l_Lake_DSL_cmdDo___closed__8();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__8);
l_Lake_DSL_cmdDo___closed__9 = _init_l_Lake_DSL_cmdDo___closed__9();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__9);
l_Lake_DSL_cmdDo___closed__10 = _init_l_Lake_DSL_cmdDo___closed__10();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__10);
l_Lake_DSL_cmdDo___closed__11 = _init_l_Lake_DSL_cmdDo___closed__11();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__11);
l_Lake_DSL_cmdDo___closed__12 = _init_l_Lake_DSL_cmdDo___closed__12();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__12);
l_Lake_DSL_cmdDo___closed__13 = _init_l_Lake_DSL_cmdDo___closed__13();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__13);
l_Lake_DSL_cmdDo___closed__14 = _init_l_Lake_DSL_cmdDo___closed__14();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__14);
l_Lake_DSL_cmdDo___closed__15 = _init_l_Lake_DSL_cmdDo___closed__15();
lean_mark_persistent(l_Lake_DSL_cmdDo___closed__15);
l_Lake_DSL_cmdDo = _init_l_Lake_DSL_cmdDo();
lean_mark_persistent(l_Lake_DSL_cmdDo);
l_Lake_DSL_metaIf___closed__0 = _init_l_Lake_DSL_metaIf___closed__0();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__0);
l_Lake_DSL_metaIf___closed__1 = _init_l_Lake_DSL_metaIf___closed__1();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__1);
l_Lake_DSL_metaIf___closed__2 = _init_l_Lake_DSL_metaIf___closed__2();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__2);
l_Lake_DSL_metaIf___closed__3 = _init_l_Lake_DSL_metaIf___closed__3();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__3);
l_Lake_DSL_metaIf___closed__4 = _init_l_Lake_DSL_metaIf___closed__4();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__4);
l_Lake_DSL_metaIf___closed__5 = _init_l_Lake_DSL_metaIf___closed__5();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__5);
l_Lake_DSL_metaIf___closed__6 = _init_l_Lake_DSL_metaIf___closed__6();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__6);
l_Lake_DSL_metaIf___closed__7 = _init_l_Lake_DSL_metaIf___closed__7();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__7);
l_Lake_DSL_metaIf___closed__8 = _init_l_Lake_DSL_metaIf___closed__8();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__8);
l_Lake_DSL_metaIf___closed__9 = _init_l_Lake_DSL_metaIf___closed__9();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__9);
l_Lake_DSL_metaIf___closed__10 = _init_l_Lake_DSL_metaIf___closed__10();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__10);
l_Lake_DSL_metaIf___closed__11 = _init_l_Lake_DSL_metaIf___closed__11();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__11);
l_Lake_DSL_metaIf___closed__12 = _init_l_Lake_DSL_metaIf___closed__12();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__12);
l_Lake_DSL_metaIf___closed__13 = _init_l_Lake_DSL_metaIf___closed__13();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__13);
l_Lake_DSL_metaIf___closed__14 = _init_l_Lake_DSL_metaIf___closed__14();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__14);
l_Lake_DSL_metaIf___closed__15 = _init_l_Lake_DSL_metaIf___closed__15();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__15);
l_Lake_DSL_metaIf___closed__16 = _init_l_Lake_DSL_metaIf___closed__16();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__16);
l_Lake_DSL_metaIf___closed__17 = _init_l_Lake_DSL_metaIf___closed__17();
lean_mark_persistent(l_Lake_DSL_metaIf___closed__17);
l_Lake_DSL_metaIf = _init_l_Lake_DSL_metaIf();
lean_mark_persistent(l_Lake_DSL_metaIf);
l_Lake_DSL_runIO___closed__0 = _init_l_Lake_DSL_runIO___closed__0();
lean_mark_persistent(l_Lake_DSL_runIO___closed__0);
l_Lake_DSL_runIO___closed__1 = _init_l_Lake_DSL_runIO___closed__1();
lean_mark_persistent(l_Lake_DSL_runIO___closed__1);
l_Lake_DSL_runIO___closed__2 = _init_l_Lake_DSL_runIO___closed__2();
lean_mark_persistent(l_Lake_DSL_runIO___closed__2);
l_Lake_DSL_runIO___closed__3 = _init_l_Lake_DSL_runIO___closed__3();
lean_mark_persistent(l_Lake_DSL_runIO___closed__3);
l_Lake_DSL_runIO___closed__4 = _init_l_Lake_DSL_runIO___closed__4();
lean_mark_persistent(l_Lake_DSL_runIO___closed__4);
l_Lake_DSL_runIO___closed__5 = _init_l_Lake_DSL_runIO___closed__5();
lean_mark_persistent(l_Lake_DSL_runIO___closed__5);
l_Lake_DSL_runIO___closed__6 = _init_l_Lake_DSL_runIO___closed__6();
lean_mark_persistent(l_Lake_DSL_runIO___closed__6);
l_Lake_DSL_runIO___closed__7 = _init_l_Lake_DSL_runIO___closed__7();
lean_mark_persistent(l_Lake_DSL_runIO___closed__7);
l_Lake_DSL_runIO___closed__8 = _init_l_Lake_DSL_runIO___closed__8();
lean_mark_persistent(l_Lake_DSL_runIO___closed__8);
l_Lake_DSL_runIO = _init_l_Lake_DSL_runIO();
lean_mark_persistent(l_Lake_DSL_runIO);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
