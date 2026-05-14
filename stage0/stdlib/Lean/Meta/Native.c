// Lean compiler output
// Module: Lean.Meta.Native
// Imports: public import Lean.Meta.Basic import Lean.Util.CollectLevelParams import Lean.Elab.DeclarationRange import Lean.Compiler.Options
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "` failed: Could not evaluate decidable instance. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` failed. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__10;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__11;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__0;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__1;
static const lean_array_object l_Lean_Meta_nativeEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__2 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__2_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__3;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_native"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__4_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 17, 188, 127, 248, 12, 59, 169)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__5 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__5_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "decl"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__6 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__6_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__6_value),LEAN_SCALAR_PTR_LITERAL(122, 197, 108, 116, 168, 105, 88, 191)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__7 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__7_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ax"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__8 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__8_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__8_value),LEAN_SCALAR_PTR_LITERAL(79, 222, 122, 135, 172, 245, 68, 224)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__9 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__9_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__10 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__10_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__11 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__11_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__12;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__13;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__14;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__15;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__16 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__16_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__16_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__17 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__17_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__18;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` failed: Cannot native decide proposition with metavariables:"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__19 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__19_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__20;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` failed: Cannot native decide proposition with free variables:"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__21 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__21_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_prf_8_; lean_object* v___x_9_; 
v_prf_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_prf_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_prf_8_);
return v___x_9_;
}
else
{
return v_k_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object* v_t_22_, lean_object* v_success_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_22_, v_success_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_success_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_26_, v_success_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object* v_t_30_, lean_object* v_notTrue_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_30_, v_notTrue_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_notTrue_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_34_, v_notTrue_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = l_Lean_Elab_abortCommandExceptionId;
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; lean_object* v_env_53_; lean_object* v___x_54_; lean_object* v_mctx_55_; lean_object* v_lctx_56_; lean_object* v_options_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_52_ = lean_st_ref_get(v___y_50_);
v_env_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc_ref(v_env_53_);
lean_dec(v___x_52_);
v___x_54_ = lean_st_ref_get(v___y_48_);
v_mctx_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_mctx_55_);
lean_dec(v___x_54_);
v_lctx_56_ = lean_ctor_get(v___y_47_, 2);
v_options_57_ = lean_ctor_get(v___y_49_, 2);
lean_inc_ref(v_options_57_);
lean_inc_ref(v_lctx_56_);
v___x_58_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_58_, 0, v_env_53_);
lean_ctor_set(v___x_58_, 1, v_mctx_55_);
lean_ctor_set(v___x_58_, 2, v_lctx_56_);
lean_ctor_set(v___x_58_, 3, v_options_57_);
v___x_59_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v_msgData_46_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_ref_74_; lean_object* v___x_75_; lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_ref_74_ = lean_ctor_get(v___y_71_, 5);
v___x_75_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
lean_inc(v_ref_74_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_ref_74_);
lean_ctor_set(v___x_80_, 1, v_a_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 1);
lean_ctor_set(v___x_78_, 0, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(lean_object* v_x_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_98_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_a_98_);
lean_dec_ref(v_x_92_);
v___x_99_ = l_Lean_stringToMessageData(v_a_98_);
v___x_100_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_99_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
return v___x_100_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v_x_92_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v_x_92_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v_x_92_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 0);
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(lean_object* v_constName_116_, uint8_t v_checkMeta_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; lean_object* v_env_124_; uint8_t v___x_125_; 
v___x_123_ = lean_st_ref_get(v___y_121_);
v_env_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc_ref(v_env_124_);
lean_dec(v___x_123_);
lean_inc(v_constName_116_);
v___x_125_ = lean_has_compile_error(v_env_124_, v_constName_116_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v_env_127_; lean_object* v_options_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = lean_st_ref_get(v___y_121_);
v_env_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_127_);
lean_dec(v___x_126_);
v_options_128_ = lean_ctor_get(v___y_120_, 2);
v___x_129_ = l_Lean_Environment_evalConst___redArg(v_env_127_, v_options_128_, v_constName_116_, v_checkMeta_117_);
lean_dec(v_constName_116_);
lean_dec_ref(v_env_127_);
v___x_130_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_129_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; lean_object* v_env_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec_ref(v___x_131_);
v___x_132_ = lean_st_ref_get(v___y_121_);
v_env_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_env_133_);
lean_dec(v___x_132_);
v_options_134_ = lean_ctor_get(v___y_120_, 2);
v___x_135_ = l_Lean_Environment_evalConst___redArg(v_env_133_, v_options_134_, v_constName_116_, v_checkMeta_117_);
lean_dec(v_constName_116_);
lean_dec_ref(v_env_133_);
v___x_136_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_135_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
return v___x_136_;
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v_constName_116_);
v_a_137_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_131_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_131_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg___boxed(lean_object* v_constName_145_, lean_object* v_checkMeta_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v_checkMeta_boxed_152_; lean_object* v_res_153_; 
v_checkMeta_boxed_152_ = lean_unbox(v_checkMeta_146_);
v_res_153_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_145_, v_checkMeta_boxed_152_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object* v_auxDeclName_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___x_160_; lean_object* v___x_161_; 
v___x_160_ = 1;
v___x_161_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_auxDeclName_154_, v___x_160_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object* v_auxDeclName_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_auxDeclName_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(lean_object* v_00_u03b1_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(lean_object* v_00_u03b1_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(v_00_u03b1_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(lean_object* v_00_u03b1_183_, lean_object* v_constName_184_, uint8_t v_checkMeta_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_184_, v_checkMeta_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_192_, lean_object* v_constName_193_, lean_object* v_checkMeta_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
uint8_t v_checkMeta_boxed_200_; lean_object* v_res_201_; 
v_checkMeta_boxed_200_ = lean_unbox(v_checkMeta_194_);
v_res_201_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(v_00_u03b1_192_, v_constName_193_, v_checkMeta_boxed_200_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b1_202_, lean_object* v_x_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b1_210_, lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(v_00_u03b1_210_, v_x_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_218_, lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_226_, v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object* v_e_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = l_Lean_Expr_hasMVar(v_e_234_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_e_234_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v_mctx_240_; lean_object* v___x_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; lean_object* v_cache_245_; lean_object* v_zetaDeltaFVarIds_246_; lean_object* v_postponed_247_; lean_object* v_diag_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_257_; 
v___x_239_ = lean_st_ref_get(v___y_235_);
v_mctx_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_mctx_240_);
lean_dec(v___x_239_);
v___x_241_ = l_Lean_instantiateMVarsCore(v_mctx_240_, v_e_234_);
v_fst_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_fst_242_);
v_snd_243_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v___x_241_);
v___x_244_ = lean_st_ref_take(v___y_235_);
v_cache_245_ = lean_ctor_get(v___x_244_, 1);
v_zetaDeltaFVarIds_246_ = lean_ctor_get(v___x_244_, 2);
v_postponed_247_ = lean_ctor_get(v___x_244_, 3);
v_diag_248_ = lean_ctor_get(v___x_244_, 4);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_244_, 0);
lean_dec(v_unused_258_);
v___x_250_ = v___x_244_;
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_diag_248_);
lean_inc(v_postponed_247_);
lean_inc(v_zetaDeltaFVarIds_246_);
lean_inc(v_cache_245_);
lean_dec(v___x_244_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v_snd_243_);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_snd_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_cache_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_zetaDeltaFVarIds_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_postponed_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_diag_248_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_st_ref_set(v___y_235_, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_fst_242_);
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object* v_e_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_259_, v___y_260_);
lean_dec(v___y_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object* v_e_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_263_, v___y_265_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object* v_e_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(v_e_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object* v_kind_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; lean_object* v_auxDeclNGen_281_; lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v___x_284_; lean_object* v_fst_285_; lean_object* v_snd_286_; lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_traceState_291_; lean_object* v_cache_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v_newDecls_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_305_; 
v___x_280_ = lean_st_ref_get(v___y_278_);
v_auxDeclNGen_281_ = lean_ctor_get(v___x_280_, 3);
lean_inc_ref(v_auxDeclNGen_281_);
lean_dec(v___x_280_);
v___x_282_ = lean_st_ref_get(v___y_278_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_env_283_);
lean_dec(v___x_282_);
v___x_284_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_283_, v_auxDeclNGen_281_, v_kind_277_);
v_fst_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_fst_285_);
v_snd_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_snd_286_);
lean_dec_ref(v___x_284_);
v___x_287_ = lean_st_ref_take(v___y_278_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_289_ = lean_ctor_get(v___x_287_, 1);
v_ngen_290_ = lean_ctor_get(v___x_287_, 2);
v_traceState_291_ = lean_ctor_get(v___x_287_, 4);
v_cache_292_ = lean_ctor_get(v___x_287_, 5);
v_messages_293_ = lean_ctor_get(v___x_287_, 6);
v_infoState_294_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_295_ = lean_ctor_get(v___x_287_, 8);
v_newDecls_296_ = lean_ctor_get(v___x_287_, 9);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_287_, 3);
lean_dec(v_unused_306_);
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_newDecls_296_);
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_cache_292_);
lean_inc(v_traceState_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 3, v_snd_286_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_env_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_snd_286_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_traceState_291_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_cache_292_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_snapshotTasks_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 9, v_newDecls_296_);
v___x_301_ = v_reuseFailAlloc_304_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_st_ref_set(v___y_278_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_fst_285_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_307_, v___y_308_);
lean_dec(v___y_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_311_, v___y_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_324_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_opts_325_, lean_object* v_opt_326_){
_start:
{
lean_object* v_name_327_; lean_object* v_defValue_328_; lean_object* v_map_329_; lean_object* v___x_330_; 
v_name_327_ = lean_ctor_get(v_opt_326_, 0);
v_defValue_328_ = lean_ctor_get(v_opt_326_, 1);
v_map_329_ = lean_ctor_get(v_opts_325_, 0);
v___x_330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_329_, v_name_327_);
if (lean_obj_tag(v___x_330_) == 0)
{
uint8_t v___x_331_; 
v___x_331_ = lean_unbox(v_defValue_328_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; 
v_val_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_332_);
lean_dec_ref(v___x_330_);
if (lean_obj_tag(v_val_332_) == 1)
{
uint8_t v_v_333_; 
v_v_333_ = lean_ctor_get_uint8(v_val_332_, 0);
lean_dec_ref(v_val_332_);
return v_v_333_;
}
else
{
uint8_t v___x_334_; 
lean_dec(v_val_332_);
v___x_334_ = lean_unbox(v_defValue_328_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_opts_335_, lean_object* v_opt_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v_opts_335_, v_opt_336_);
lean_dec_ref(v_opt_336_);
lean_dec_ref(v_opts_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_339_, lean_object* v_opt_340_){
_start:
{
lean_object* v_name_341_; lean_object* v_defValue_342_; lean_object* v_map_343_; lean_object* v___x_344_; 
v_name_341_ = lean_ctor_get(v_opt_340_, 0);
v_defValue_342_ = lean_ctor_get(v_opt_340_, 1);
v_map_343_ = lean_ctor_get(v_opts_339_, 0);
v___x_344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_343_, v_name_341_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_inc(v_defValue_342_);
return v_defValue_342_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___x_344_);
if (lean_obj_tag(v_val_345_) == 3)
{
lean_object* v_v_346_; 
v_v_346_ = lean_ctor_get(v_val_345_, 0);
lean_inc(v_v_346_);
lean_dec_ref(v_val_345_);
return v_v_346_;
}
else
{
lean_dec(v_val_345_);
lean_inc(v_defValue_342_);
return v_defValue_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_o_353_, lean_object* v_k_354_, uint8_t v_v_355_){
_start:
{
lean_object* v_map_356_; uint8_t v_hasTrace_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_371_; 
v_map_356_ = lean_ctor_get(v_o_353_, 0);
v_hasTrace_357_ = lean_ctor_get_uint8(v_o_353_, sizeof(void*)*1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_o_353_);
if (v_isSharedCheck_371_ == 0)
{
v___x_359_ = v_o_353_;
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_map_356_);
lean_dec(v_o_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_361_, 0, v_v_355_);
lean_inc(v_k_354_);
v___x_362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_354_, v___x_361_, v_map_356_);
if (v_hasTrace_357_ == 0)
{
lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_366_; 
v___x_363_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1));
v___x_364_ = l_Lean_Name_isPrefixOf(v___x_363_, v_k_354_);
lean_dec(v_k_354_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_362_);
v___x_366_ = v___x_359_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_362_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_364_);
return v___x_366_;
}
}
else
{
lean_object* v___x_369_; 
lean_dec(v_k_354_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_362_);
v___x_369_ = v___x_359_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_362_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*1, v_hasTrace_357_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_o_372_, lean_object* v_k_373_, lean_object* v_v_374_){
_start:
{
uint8_t v_v_boxed_375_; lean_object* v_res_376_; 
v_v_boxed_375_ = lean_unbox(v_v_374_);
v_res_376_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_o_372_, v_k_373_, v_v_boxed_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_opts_377_, lean_object* v_opt_378_, uint8_t v_val_379_){
_start:
{
lean_object* v_name_380_; lean_object* v___x_381_; 
v_name_380_ = lean_ctor_get(v_opt_378_, 0);
lean_inc(v_name_380_);
lean_dec_ref(v_opt_378_);
v___x_381_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_opts_377_, v_name_380_, v_val_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_opts_382_, lean_object* v_opt_383_, lean_object* v_val_384_){
_start:
{
uint8_t v_val_boxed_385_; lean_object* v_res_386_; 
v_val_boxed_385_ = lean_unbox(v_val_384_);
v_res_386_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_opts_382_, v_opt_383_, v_val_boxed_385_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_401_ = l_Lean_mkConst(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_408_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_407_);
lean_ctor_set(v___x_408_, 3, v___x_407_);
lean_ctor_set(v___x_408_, 4, v___x_407_);
lean_ctor_set(v___x_408_, 5, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_tacticName_412_, lean_object* v_a_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v___x_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_704_; 
v___x_431_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_409_, v___y_417_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_704_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_704_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_704_;
goto v_resetjp_433_;
}
v___jp_419_:
{
if (v___y_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v___y_420_);
v___x_423_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_424_ = l_Lean_MessageData_ofName(v_tacticName_412_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Exception_toMessageData(v___y_421_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_429_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec_ref(v___y_416_);
return v___x_430_;
}
else
{
lean_dec_ref(v___y_421_);
lean_dec_ref(v___y_416_);
lean_dec(v_tacticName_412_);
return v___y_420_;
}
}
v_resetjp_433_:
{
lean_object* v___y_437_; lean_object* v___y_451_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_traceState_467_; lean_object* v_messages_468_; lean_object* v_infoState_469_; lean_object* v_snapshotTasks_470_; lean_object* v_newDecls_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_702_; 
v___x_462_ = lean_st_ref_take(v___y_417_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
v_nextMacroScope_464_ = lean_ctor_get(v___x_462_, 1);
v_ngen_465_ = lean_ctor_get(v___x_462_, 2);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_462_, 3);
v_traceState_467_ = lean_ctor_get(v___x_462_, 4);
v_messages_468_ = lean_ctor_get(v___x_462_, 6);
v_infoState_469_ = lean_ctor_get(v___x_462_, 7);
v_snapshotTasks_470_ = lean_ctor_get(v___x_462_, 8);
v_newDecls_471_ = lean_ctor_get(v___x_462_, 9);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v___x_462_, 5);
lean_dec(v_unused_703_);
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_702_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_newDecls_471_);
lean_inc(v_snapshotTasks_470_);
lean_inc(v_infoState_469_);
lean_inc(v_messages_468_);
lean_inc(v_traceState_467_);
lean_inc(v_auxDeclNGen_466_);
lean_inc(v_ngen_465_);
lean_inc(v_nextMacroScope_464_);
lean_inc(v_env_463_);
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_702_;
goto v_resetjp_472_;
}
v___jp_436_:
{
if (lean_obj_tag(v___y_437_) == 0)
{
lean_object* v___x_438_; 
lean_dec_ref(v___y_437_);
v___x_438_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_a_432_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_dec_ref(v___y_416_);
lean_dec(v_tacticName_412_);
return v___x_438_;
}
else
{
lean_object* v_a_439_; uint8_t v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
v___x_440_ = l_Lean_Exception_isInterrupt(v_a_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
lean_inc(v_a_439_);
v___x_441_ = l_Lean_Exception_isRuntime(v_a_439_);
v___y_420_ = v___x_438_;
v___y_421_ = v_a_439_;
v___y_422_ = v___x_441_;
goto v___jp_419_;
}
else
{
v___y_420_ = v___x_438_;
v___y_421_ = v_a_439_;
v___y_422_ = v___x_440_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_a_432_);
lean_dec_ref(v___y_416_);
lean_dec(v_tacticName_412_);
v_a_442_ = lean_ctor_get(v___y_437_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___y_437_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___y_437_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___y_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
v___jp_450_:
{
if (v___y_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec_ref(v___y_451_);
v___x_454_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_412_);
v___x_455_ = l_Lean_MessageData_ofName(v_tacticName_412_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_Exception_toMessageData(v___y_452_);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_460_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_437_ = v___x_461_;
goto v___jp_436_;
}
else
{
lean_dec_ref(v___y_452_);
v___y_437_ = v___y_451_;
goto v___jp_436_;
}
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_475_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_432_, 3);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_a_432_);
lean_ctor_set(v___x_476_, 1, v___x_410_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_a_432_);
lean_ctor_set(v___x_477_, 1, v___x_411_);
v___x_478_ = l_Lean_markMeta(v_env_463_, v_a_432_);
v___x_479_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 5, v___x_479_);
lean_ctor_set(v___x_473_, 0, v___x_478_);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_nextMacroScope_464_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_ngen_465_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_auxDeclNGen_466_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_traceState_467_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_infoState_469_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_snapshotTasks_470_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v_newDecls_471_);
v___x_481_ = v_reuseFailAlloc_701_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_mctx_484_; lean_object* v_zetaDeltaFVarIds_485_; lean_object* v_postponed_486_; lean_object* v_diag_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_699_; 
v___x_482_ = lean_st_ref_set(v___y_417_, v___x_481_);
v___x_483_ = lean_st_ref_take(v___y_415_);
v_mctx_484_ = lean_ctor_get(v___x_483_, 0);
v_zetaDeltaFVarIds_485_ = lean_ctor_get(v___x_483_, 2);
v_postponed_486_ = lean_ctor_get(v___x_483_, 3);
v_diag_487_ = lean_ctor_get(v___x_483_, 4);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_483_, 1);
lean_dec(v_unused_700_);
v___x_489_ = v___x_483_;
v_isShared_490_ = v_isSharedCheck_699_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_diag_487_);
lean_inc(v_postponed_486_);
lean_inc(v_zetaDeltaFVarIds_485_);
lean_inc(v_mctx_484_);
lean_dec(v___x_483_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_699_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_mctx_484_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_zetaDeltaFVarIds_485_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_postponed_486_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_diag_487_);
v___x_493_ = v_reuseFailAlloc_698_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_options_496_; lean_object* v_env_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_494_ = lean_st_ref_set(v___y_415_, v___x_493_);
v___x_495_ = lean_st_ref_get(v___y_417_);
v_options_496_ = lean_ctor_get(v___y_416_, 2);
v_env_497_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(1);
v___x_499_ = 1;
v___x_500_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_500_, 0, v___x_476_);
lean_ctor_set(v___x_500_, 1, v_a_413_);
lean_ctor_set(v___x_500_, 2, v___x_498_);
lean_ctor_set(v___x_500_, 3, v___x_477_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*4, v___x_499_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 0, v___x_500_);
v___x_502_ = v___x_434_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_697_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
uint8_t v___x_503_; uint8_t v___x_504_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v_fileName_509_; lean_object* v_fileMap_510_; lean_object* v_currRecDepth_511_; lean_object* v_ref_512_; lean_object* v_currNamespace_513_; lean_object* v_openDecls_514_; lean_object* v_initHeartbeats_515_; lean_object* v_maxHeartbeats_516_; lean_object* v_quotContext_517_; lean_object* v_currMacroScope_518_; lean_object* v_cancelTk_x3f_519_; uint8_t v_suppressElabErrors_520_; lean_object* v_inheritedTraceOptions_521_; lean_object* v___y_522_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_549_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; uint8_t v___y_554_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; uint8_t v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; uint8_t v___y_619_; uint8_t v___x_640_; lean_object* v___y_642_; lean_object* v___y_643_; uint8_t v___y_675_; uint8_t v___x_696_; 
v___x_503_ = 1;
v___x_504_ = 0;
v___x_575_ = l_Lean_Elab_async;
lean_inc_ref(v_options_496_);
v___x_576_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_options_496_, v___x_575_, v___x_504_);
v___x_577_ = l_Lean_diagnostics;
v___x_640_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_576_, v___x_577_);
v___x_696_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_497_);
lean_dec_ref(v_env_497_);
if (v___x_696_ == 0)
{
if (v___x_640_ == 0)
{
lean_inc_ref(v___y_416_);
v___y_642_ = v___y_416_;
v___y_643_ = v___y_417_;
goto v___jp_641_;
}
else
{
v___y_675_ = v___x_696_;
goto v___jp_674_;
}
}
else
{
v___y_675_ = v___x_640_;
goto v___jp_674_;
}
v___jp_505_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_506_, v___y_508_);
v___x_524_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_524_, 0, v_fileName_509_);
lean_ctor_set(v___x_524_, 1, v_fileMap_510_);
lean_ctor_set(v___x_524_, 2, v___y_506_);
lean_ctor_set(v___x_524_, 3, v_currRecDepth_511_);
lean_ctor_set(v___x_524_, 4, v___x_523_);
lean_ctor_set(v___x_524_, 5, v_ref_512_);
lean_ctor_set(v___x_524_, 6, v_currNamespace_513_);
lean_ctor_set(v___x_524_, 7, v_openDecls_514_);
lean_ctor_set(v___x_524_, 8, v_initHeartbeats_515_);
lean_ctor_set(v___x_524_, 9, v_maxHeartbeats_516_);
lean_ctor_set(v___x_524_, 10, v_quotContext_517_);
lean_ctor_set(v___x_524_, 11, v_currMacroScope_518_);
lean_ctor_set(v___x_524_, 12, v_cancelTk_x3f_519_);
lean_ctor_set(v___x_524_, 13, v_inheritedTraceOptions_521_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*14, v___y_507_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*14 + 1, v_suppressElabErrors_520_);
v___x_525_ = l_Lean_addAndCompile(v___x_502_, v___x_503_, v___x_504_, v___x_524_, v___y_522_);
lean_dec_ref(v___x_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
v___y_437_ = v___x_525_;
goto v___jp_436_;
}
else
{
lean_object* v_a_526_; uint8_t v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
v___x_527_ = l_Lean_Exception_isInterrupt(v_a_526_);
if (v___x_527_ == 0)
{
uint8_t v___x_528_; 
lean_inc(v_a_526_);
v___x_528_ = l_Lean_Exception_isRuntime(v_a_526_);
v___y_451_ = v___x_525_;
v___y_452_ = v_a_526_;
v___y_453_ = v___x_528_;
goto v___jp_450_;
}
else
{
v___y_451_ = v___x_525_;
v___y_452_ = v_a_526_;
v___y_453_ = v___x_527_;
goto v___jp_450_;
}
}
}
v___jp_529_:
{
lean_object* v_fileName_535_; lean_object* v_fileMap_536_; lean_object* v_currRecDepth_537_; lean_object* v_ref_538_; lean_object* v_currNamespace_539_; lean_object* v_openDecls_540_; lean_object* v_initHeartbeats_541_; lean_object* v_maxHeartbeats_542_; lean_object* v_quotContext_543_; lean_object* v_currMacroScope_544_; lean_object* v_cancelTk_x3f_545_; uint8_t v_suppressElabErrors_546_; lean_object* v_inheritedTraceOptions_547_; 
v_fileName_535_ = lean_ctor_get(v___y_533_, 0);
lean_inc_ref(v_fileName_535_);
v_fileMap_536_ = lean_ctor_get(v___y_533_, 1);
lean_inc_ref(v_fileMap_536_);
v_currRecDepth_537_ = lean_ctor_get(v___y_533_, 3);
lean_inc(v_currRecDepth_537_);
v_ref_538_ = lean_ctor_get(v___y_533_, 5);
lean_inc(v_ref_538_);
v_currNamespace_539_ = lean_ctor_get(v___y_533_, 6);
lean_inc(v_currNamespace_539_);
v_openDecls_540_ = lean_ctor_get(v___y_533_, 7);
lean_inc(v_openDecls_540_);
v_initHeartbeats_541_ = lean_ctor_get(v___y_533_, 8);
lean_inc(v_initHeartbeats_541_);
v_maxHeartbeats_542_ = lean_ctor_get(v___y_533_, 9);
lean_inc(v_maxHeartbeats_542_);
v_quotContext_543_ = lean_ctor_get(v___y_533_, 10);
lean_inc(v_quotContext_543_);
v_currMacroScope_544_ = lean_ctor_get(v___y_533_, 11);
lean_inc(v_currMacroScope_544_);
v_cancelTk_x3f_545_ = lean_ctor_get(v___y_533_, 12);
lean_inc(v_cancelTk_x3f_545_);
v_suppressElabErrors_546_ = lean_ctor_get_uint8(v___y_533_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_547_ = lean_ctor_get(v___y_533_, 13);
lean_inc_ref(v_inheritedTraceOptions_547_);
lean_dec_ref(v___y_533_);
v___y_506_ = v___y_530_;
v___y_507_ = v___y_531_;
v___y_508_ = v___y_532_;
v_fileName_509_ = v_fileName_535_;
v_fileMap_510_ = v_fileMap_536_;
v_currRecDepth_511_ = v_currRecDepth_537_;
v_ref_512_ = v_ref_538_;
v_currNamespace_513_ = v_currNamespace_539_;
v_openDecls_514_ = v_openDecls_540_;
v_initHeartbeats_515_ = v_initHeartbeats_541_;
v_maxHeartbeats_516_ = v_maxHeartbeats_542_;
v_quotContext_517_ = v_quotContext_543_;
v_currMacroScope_518_ = v_currMacroScope_544_;
v_cancelTk_x3f_519_ = v_cancelTk_x3f_545_;
v_suppressElabErrors_520_ = v_suppressElabErrors_546_;
v_inheritedTraceOptions_521_ = v_inheritedTraceOptions_547_;
v___y_522_ = v___y_534_;
goto v___jp_505_;
}
v___jp_548_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_traceState_560_; lean_object* v_messages_561_; lean_object* v_infoState_562_; lean_object* v_snapshotTasks_563_; lean_object* v_newDecls_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v___x_555_ = lean_st_ref_take(v___y_552_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_555_, 1);
v_ngen_558_ = lean_ctor_get(v___x_555_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_555_, 3);
v_traceState_560_ = lean_ctor_get(v___x_555_, 4);
v_messages_561_ = lean_ctor_get(v___x_555_, 6);
v_infoState_562_ = lean_ctor_get(v___x_555_, 7);
v_snapshotTasks_563_ = lean_ctor_get(v___x_555_, 8);
v_newDecls_564_ = lean_ctor_get(v___x_555_, 9);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_555_, 5);
lean_dec(v_unused_574_);
v___x_566_ = v___x_555_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_newDecls_564_);
lean_inc(v_snapshotTasks_563_);
lean_inc(v_infoState_562_);
lean_inc(v_messages_561_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_555_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Kernel_enableDiag(v_env_556_, v___y_550_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 5, v___x_479_);
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_traceState_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_messages_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_infoState_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_snapshotTasks_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v_newDecls_564_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_st_ref_set(v___y_552_, v___x_570_);
v___y_530_ = v___y_549_;
v___y_531_ = v___y_550_;
v___y_532_ = v___y_551_;
v___y_533_ = v___y_553_;
v___y_534_ = v___y_552_;
goto v___jp_529_;
}
}
}
else
{
v___y_530_ = v___y_549_;
v___y_531_ = v___y_550_;
v___y_532_ = v___y_551_;
v___y_533_ = v___y_553_;
v___y_534_ = v___y_552_;
goto v___jp_529_;
}
}
v___jp_578_:
{
lean_object* v___x_584_; lean_object* v_fileName_585_; lean_object* v_fileMap_586_; lean_object* v_currRecDepth_587_; lean_object* v_ref_588_; lean_object* v_currNamespace_589_; lean_object* v_openDecls_590_; lean_object* v_initHeartbeats_591_; lean_object* v_maxHeartbeats_592_; lean_object* v_quotContext_593_; lean_object* v_currMacroScope_594_; lean_object* v_cancelTk_x3f_595_; uint8_t v_suppressElabErrors_596_; lean_object* v_inheritedTraceOptions_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v___x_584_ = lean_st_ref_get(v___y_583_);
v_fileName_585_ = lean_ctor_get(v___y_582_, 0);
v_fileMap_586_ = lean_ctor_get(v___y_582_, 1);
v_currRecDepth_587_ = lean_ctor_get(v___y_582_, 3);
v_ref_588_ = lean_ctor_get(v___y_582_, 5);
v_currNamespace_589_ = lean_ctor_get(v___y_582_, 6);
v_openDecls_590_ = lean_ctor_get(v___y_582_, 7);
v_initHeartbeats_591_ = lean_ctor_get(v___y_582_, 8);
v_maxHeartbeats_592_ = lean_ctor_get(v___y_582_, 9);
v_quotContext_593_ = lean_ctor_get(v___y_582_, 10);
v_currMacroScope_594_ = lean_ctor_get(v___y_582_, 11);
v_cancelTk_x3f_595_ = lean_ctor_get(v___y_582_, 12);
v_suppressElabErrors_596_ = lean_ctor_get_uint8(v___y_582_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_597_ = lean_ctor_get(v___y_582_, 13);
v_isSharedCheck_610_ = !lean_is_exclusive(v___y_582_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; 
v_unused_611_ = lean_ctor_get(v___y_582_, 4);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v___y_582_, 2);
lean_dec(v_unused_612_);
v___x_599_ = v___y_582_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_inheritedTraceOptions_597_);
lean_inc(v_cancelTk_x3f_595_);
lean_inc(v_currMacroScope_594_);
lean_inc(v_quotContext_593_);
lean_inc(v_maxHeartbeats_592_);
lean_inc(v_initHeartbeats_591_);
lean_inc(v_openDecls_590_);
lean_inc(v_currNamespace_589_);
lean_inc(v_ref_588_);
lean_inc(v_currRecDepth_587_);
lean_inc(v_fileMap_586_);
lean_inc(v_fileName_585_);
lean_dec(v___y_582_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_env_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v_env_601_ = lean_ctor_get(v___x_584_, 0);
lean_inc_ref(v_env_601_);
lean_dec(v___x_584_);
v___x_602_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_581_, v___y_580_);
lean_inc_ref(v_inheritedTraceOptions_597_);
lean_inc(v_cancelTk_x3f_595_);
lean_inc(v_currMacroScope_594_);
lean_inc(v_quotContext_593_);
lean_inc(v_maxHeartbeats_592_);
lean_inc(v_initHeartbeats_591_);
lean_inc(v_openDecls_590_);
lean_inc(v_currNamespace_589_);
lean_inc(v_ref_588_);
lean_inc(v_currRecDepth_587_);
lean_inc_ref(v___y_581_);
lean_inc_ref(v_fileMap_586_);
lean_inc_ref(v_fileName_585_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 4, v___x_602_);
lean_ctor_set(v___x_599_, 2, v___y_581_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_fileName_585_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_fileMap_586_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v___y_581_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_currRecDepth_587_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v_ref_588_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_currNamespace_589_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_openDecls_590_);
lean_ctor_set(v_reuseFailAlloc_609_, 8, v_initHeartbeats_591_);
lean_ctor_set(v_reuseFailAlloc_609_, 9, v_maxHeartbeats_592_);
lean_ctor_set(v_reuseFailAlloc_609_, 10, v_quotContext_593_);
lean_ctor_set(v_reuseFailAlloc_609_, 11, v_currMacroScope_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 12, v_cancelTk_x3f_595_);
lean_ctor_set(v_reuseFailAlloc_609_, 13, v_inheritedTraceOptions_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_609_, sizeof(void*)*14 + 1, v_suppressElabErrors_596_);
v___x_604_ = v_reuseFailAlloc_609_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; 
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*14, v___y_579_);
v___x_605_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_606_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___y_581_, v___x_605_, v___x_503_);
v___x_607_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_606_, v___x_577_);
v___x_608_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_601_);
lean_dec_ref(v_env_601_);
if (v___x_608_ == 0)
{
if (v___x_607_ == 0)
{
lean_dec_ref(v___x_604_);
v___y_506_ = v___x_606_;
v___y_507_ = v___x_607_;
v___y_508_ = v___y_580_;
v_fileName_509_ = v_fileName_585_;
v_fileMap_510_ = v_fileMap_586_;
v_currRecDepth_511_ = v_currRecDepth_587_;
v_ref_512_ = v_ref_588_;
v_currNamespace_513_ = v_currNamespace_589_;
v_openDecls_514_ = v_openDecls_590_;
v_initHeartbeats_515_ = v_initHeartbeats_591_;
v_maxHeartbeats_516_ = v_maxHeartbeats_592_;
v_quotContext_517_ = v_quotContext_593_;
v_currMacroScope_518_ = v_currMacroScope_594_;
v_cancelTk_x3f_519_ = v_cancelTk_x3f_595_;
v_suppressElabErrors_520_ = v_suppressElabErrors_596_;
v_inheritedTraceOptions_521_ = v_inheritedTraceOptions_597_;
v___y_522_ = v___y_583_;
goto v___jp_505_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_597_);
lean_dec(v_cancelTk_x3f_595_);
lean_dec(v_currMacroScope_594_);
lean_dec(v_quotContext_593_);
lean_dec(v_maxHeartbeats_592_);
lean_dec(v_initHeartbeats_591_);
lean_dec(v_openDecls_590_);
lean_dec(v_currNamespace_589_);
lean_dec(v_ref_588_);
lean_dec(v_currRecDepth_587_);
lean_dec_ref(v_fileMap_586_);
lean_dec_ref(v_fileName_585_);
v___y_549_ = v___x_606_;
v___y_550_ = v___x_607_;
v___y_551_ = v___y_580_;
v___y_552_ = v___y_583_;
v___y_553_ = v___x_604_;
v___y_554_ = v___x_608_;
goto v___jp_548_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_597_);
lean_dec(v_cancelTk_x3f_595_);
lean_dec(v_currMacroScope_594_);
lean_dec(v_quotContext_593_);
lean_dec(v_maxHeartbeats_592_);
lean_dec(v_initHeartbeats_591_);
lean_dec(v_openDecls_590_);
lean_dec(v_currNamespace_589_);
lean_dec(v_ref_588_);
lean_dec(v_currRecDepth_587_);
lean_dec_ref(v_fileMap_586_);
lean_dec_ref(v_fileName_585_);
v___y_549_ = v___x_606_;
v___y_550_ = v___x_607_;
v___y_551_ = v___y_580_;
v___y_552_ = v___y_583_;
v___y_553_ = v___x_604_;
v___y_554_ = v___x_607_;
goto v___jp_548_;
}
}
}
}
v___jp_613_:
{
if (v___y_619_ == 0)
{
lean_object* v___x_620_; lean_object* v_env_621_; lean_object* v_nextMacroScope_622_; lean_object* v_ngen_623_; lean_object* v_auxDeclNGen_624_; lean_object* v_traceState_625_; lean_object* v_messages_626_; lean_object* v_infoState_627_; lean_object* v_snapshotTasks_628_; lean_object* v_newDecls_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
v___x_620_ = lean_st_ref_take(v___y_616_);
v_env_621_ = lean_ctor_get(v___x_620_, 0);
v_nextMacroScope_622_ = lean_ctor_get(v___x_620_, 1);
v_ngen_623_ = lean_ctor_get(v___x_620_, 2);
v_auxDeclNGen_624_ = lean_ctor_get(v___x_620_, 3);
v_traceState_625_ = lean_ctor_get(v___x_620_, 4);
v_messages_626_ = lean_ctor_get(v___x_620_, 6);
v_infoState_627_ = lean_ctor_get(v___x_620_, 7);
v_snapshotTasks_628_ = lean_ctor_get(v___x_620_, 8);
v_newDecls_629_ = lean_ctor_get(v___x_620_, 9);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v___x_620_, 5);
lean_dec(v_unused_639_);
v___x_631_ = v___x_620_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_newDecls_629_);
lean_inc(v_snapshotTasks_628_);
lean_inc(v_infoState_627_);
lean_inc(v_messages_626_);
lean_inc(v_traceState_625_);
lean_inc(v_auxDeclNGen_624_);
lean_inc(v_ngen_623_);
lean_inc(v_nextMacroScope_622_);
lean_inc(v_env_621_);
lean_dec(v___x_620_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = l_Lean_Kernel_enableDiag(v_env_621_, v___y_614_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 5, v___x_479_);
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_nextMacroScope_622_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_ngen_623_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_auxDeclNGen_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_traceState_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_messages_626_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_infoState_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_snapshotTasks_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 9, v_newDecls_629_);
v___x_635_ = v_reuseFailAlloc_637_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; 
v___x_636_ = lean_st_ref_set(v___y_616_, v___x_635_);
v___y_579_ = v___y_614_;
v___y_580_ = v___y_615_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_618_;
v___y_583_ = v___y_616_;
goto v___jp_578_;
}
}
}
else
{
v___y_579_ = v___y_614_;
v___y_580_ = v___y_615_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_618_;
v___y_583_ = v___y_616_;
goto v___jp_578_;
}
}
v___jp_641_:
{
lean_object* v___x_644_; lean_object* v_fileName_645_; lean_object* v_fileMap_646_; lean_object* v_currRecDepth_647_; lean_object* v_ref_648_; lean_object* v_currNamespace_649_; lean_object* v_openDecls_650_; lean_object* v_initHeartbeats_651_; lean_object* v_maxHeartbeats_652_; lean_object* v_quotContext_653_; lean_object* v_currMacroScope_654_; lean_object* v_cancelTk_x3f_655_; uint8_t v_suppressElabErrors_656_; lean_object* v_inheritedTraceOptions_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_671_; 
v___x_644_ = lean_st_ref_get(v___y_643_);
v_fileName_645_ = lean_ctor_get(v___y_642_, 0);
v_fileMap_646_ = lean_ctor_get(v___y_642_, 1);
v_currRecDepth_647_ = lean_ctor_get(v___y_642_, 3);
v_ref_648_ = lean_ctor_get(v___y_642_, 5);
v_currNamespace_649_ = lean_ctor_get(v___y_642_, 6);
v_openDecls_650_ = lean_ctor_get(v___y_642_, 7);
v_initHeartbeats_651_ = lean_ctor_get(v___y_642_, 8);
v_maxHeartbeats_652_ = lean_ctor_get(v___y_642_, 9);
v_quotContext_653_ = lean_ctor_get(v___y_642_, 10);
v_currMacroScope_654_ = lean_ctor_get(v___y_642_, 11);
v_cancelTk_x3f_655_ = lean_ctor_get(v___y_642_, 12);
v_suppressElabErrors_656_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_657_ = lean_ctor_get(v___y_642_, 13);
v_isSharedCheck_671_ = !lean_is_exclusive(v___y_642_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; 
v_unused_672_ = lean_ctor_get(v___y_642_, 4);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v___y_642_, 2);
lean_dec(v_unused_673_);
v___x_659_ = v___y_642_;
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_inheritedTraceOptions_657_);
lean_inc(v_cancelTk_x3f_655_);
lean_inc(v_currMacroScope_654_);
lean_inc(v_quotContext_653_);
lean_inc(v_maxHeartbeats_652_);
lean_inc(v_initHeartbeats_651_);
lean_inc(v_openDecls_650_);
lean_inc(v_currNamespace_649_);
lean_inc(v_ref_648_);
lean_inc(v_currRecDepth_647_);
lean_inc(v_fileMap_646_);
lean_inc(v_fileName_645_);
lean_dec(v___y_642_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_env_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_665_; 
v_env_661_ = lean_ctor_get(v___x_644_, 0);
lean_inc_ref(v_env_661_);
lean_dec(v___x_644_);
v___x_662_ = l_Lean_maxRecDepth;
v___x_663_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_576_, v___x_662_);
lean_inc_ref(v___x_576_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v___x_663_);
lean_ctor_set(v___x_659_, 2, v___x_576_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fileName_645_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_fileMap_646_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_currRecDepth_647_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_670_, 5, v_ref_648_);
lean_ctor_set(v_reuseFailAlloc_670_, 6, v_currNamespace_649_);
lean_ctor_set(v_reuseFailAlloc_670_, 7, v_openDecls_650_);
lean_ctor_set(v_reuseFailAlloc_670_, 8, v_initHeartbeats_651_);
lean_ctor_set(v_reuseFailAlloc_670_, 9, v_maxHeartbeats_652_);
lean_ctor_set(v_reuseFailAlloc_670_, 10, v_quotContext_653_);
lean_ctor_set(v_reuseFailAlloc_670_, 11, v_currMacroScope_654_);
lean_ctor_set(v_reuseFailAlloc_670_, 12, v_cancelTk_x3f_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 13, v_inheritedTraceOptions_657_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*14 + 1, v_suppressElabErrors_656_);
v___x_665_ = v_reuseFailAlloc_670_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; uint8_t v___x_669_; 
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*14, v___x_640_);
v___x_666_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_667_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___x_576_, v___x_666_, v___x_504_);
v___x_668_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_667_, v___x_577_);
v___x_669_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_661_);
lean_dec_ref(v_env_661_);
if (v___x_669_ == 0)
{
if (v___x_668_ == 0)
{
v___y_579_ = v___x_668_;
v___y_580_ = v___x_662_;
v___y_581_ = v___x_667_;
v___y_582_ = v___x_665_;
v___y_583_ = v___y_643_;
goto v___jp_578_;
}
else
{
v___y_614_ = v___x_668_;
v___y_615_ = v___x_662_;
v___y_616_ = v___y_643_;
v___y_617_ = v___x_667_;
v___y_618_ = v___x_665_;
v___y_619_ = v___x_669_;
goto v___jp_613_;
}
}
else
{
v___y_614_ = v___x_668_;
v___y_615_ = v___x_662_;
v___y_616_ = v___y_643_;
v___y_617_ = v___x_667_;
v___y_618_ = v___x_665_;
v___y_619_ = v___x_668_;
goto v___jp_613_;
}
}
}
}
v___jp_674_:
{
if (v___y_675_ == 0)
{
lean_object* v___x_676_; lean_object* v_env_677_; lean_object* v_nextMacroScope_678_; lean_object* v_ngen_679_; lean_object* v_auxDeclNGen_680_; lean_object* v_traceState_681_; lean_object* v_messages_682_; lean_object* v_infoState_683_; lean_object* v_snapshotTasks_684_; lean_object* v_newDecls_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
v___x_676_ = lean_st_ref_take(v___y_417_);
v_env_677_ = lean_ctor_get(v___x_676_, 0);
v_nextMacroScope_678_ = lean_ctor_get(v___x_676_, 1);
v_ngen_679_ = lean_ctor_get(v___x_676_, 2);
v_auxDeclNGen_680_ = lean_ctor_get(v___x_676_, 3);
v_traceState_681_ = lean_ctor_get(v___x_676_, 4);
v_messages_682_ = lean_ctor_get(v___x_676_, 6);
v_infoState_683_ = lean_ctor_get(v___x_676_, 7);
v_snapshotTasks_684_ = lean_ctor_get(v___x_676_, 8);
v_newDecls_685_ = lean_ctor_get(v___x_676_, 9);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_676_, 5);
lean_dec(v_unused_695_);
v___x_687_ = v___x_676_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_newDecls_685_);
lean_inc(v_snapshotTasks_684_);
lean_inc(v_infoState_683_);
lean_inc(v_messages_682_);
lean_inc(v_traceState_681_);
lean_inc(v_auxDeclNGen_680_);
lean_inc(v_ngen_679_);
lean_inc(v_nextMacroScope_678_);
lean_inc(v_env_677_);
lean_dec(v___x_676_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Lean_Kernel_enableDiag(v_env_677_, v___x_640_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 5, v___x_479_);
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_nextMacroScope_678_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_ngen_679_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_auxDeclNGen_680_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_traceState_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 5, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_693_, 6, v_messages_682_);
lean_ctor_set(v_reuseFailAlloc_693_, 7, v_infoState_683_);
lean_ctor_set(v_reuseFailAlloc_693_, 8, v_snapshotTasks_684_);
lean_ctor_set(v_reuseFailAlloc_693_, 9, v_newDecls_685_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_st_ref_set(v___y_417_, v___x_691_);
lean_inc_ref(v___y_416_);
v___y_642_ = v___y_416_;
v___y_643_ = v___y_417_;
goto v___jp_641_;
}
}
}
else
{
lean_inc_ref(v___y_416_);
v___y_642_ = v___y_416_;
v___y_643_ = v___y_417_;
goto v___jp_641_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_tacticName_708_, lean_object* v_a_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_705_, v___x_706_, v___x_707_, v_tacticName_708_, v_a_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object* v_stx_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_719_; lean_object* v___x_720_; 
v___x_719_ = 0;
v___x_720_ = l_Lean_Syntax_getRange_x3f(v_stx_716_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_733_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_733_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_fileMap_725_; lean_object* v_start_726_; lean_object* v_stop_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v_fileMap_725_ = lean_ctor_get(v___y_717_, 1);
v_start_726_ = lean_ctor_get(v_val_721_, 0);
lean_inc(v_start_726_);
v_stop_727_ = lean_ctor_get(v_val_721_, 1);
lean_inc(v_stop_727_);
lean_dec(v_val_721_);
lean_inc_ref(v_fileMap_725_);
v___x_728_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_725_, v_start_726_, v_stop_727_);
lean_dec(v_stop_727_);
lean_dec(v_start_726_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_728_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_732_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; 
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v___x_720_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object* v_stx_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_736_, v___y_737_);
lean_dec_ref(v___y_737_);
lean_dec(v_stx_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(lean_object* v_declName_740_, lean_object* v_declRanges_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Name_isAnonymous(v_declName_740_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v_env_747_; lean_object* v_nextMacroScope_748_; lean_object* v_ngen_749_; lean_object* v_auxDeclNGen_750_; lean_object* v_traceState_751_; lean_object* v_messages_752_; lean_object* v_infoState_753_; lean_object* v_snapshotTasks_754_; lean_object* v_newDecls_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_783_; 
v___x_746_ = lean_st_ref_take(v___y_743_);
v_env_747_ = lean_ctor_get(v___x_746_, 0);
v_nextMacroScope_748_ = lean_ctor_get(v___x_746_, 1);
v_ngen_749_ = lean_ctor_get(v___x_746_, 2);
v_auxDeclNGen_750_ = lean_ctor_get(v___x_746_, 3);
v_traceState_751_ = lean_ctor_get(v___x_746_, 4);
v_messages_752_ = lean_ctor_get(v___x_746_, 6);
v_infoState_753_ = lean_ctor_get(v___x_746_, 7);
v_snapshotTasks_754_ = lean_ctor_get(v___x_746_, 8);
v_newDecls_755_ = lean_ctor_get(v___x_746_, 9);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_746_, 5);
lean_dec(v_unused_784_);
v___x_757_ = v___x_746_;
v_isShared_758_ = v_isSharedCheck_783_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_newDecls_755_);
lean_inc(v_snapshotTasks_754_);
lean_inc(v_infoState_753_);
lean_inc(v_messages_752_);
lean_inc(v_traceState_751_);
lean_inc(v_auxDeclNGen_750_);
lean_inc(v_ngen_749_);
lean_inc(v_nextMacroScope_748_);
lean_inc(v_env_747_);
lean_dec(v___x_746_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_783_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_759_ = l_Lean_declRangeExt;
v___x_760_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_759_, v_env_747_, v_declName_740_, v_declRanges_741_);
v___x_761_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 5, v___x_761_);
lean_ctor_set(v___x_757_, 0, v___x_760_);
v___x_763_ = v___x_757_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_nextMacroScope_748_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_ngen_749_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_auxDeclNGen_750_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_traceState_751_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_messages_752_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_infoState_753_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_snapshotTasks_754_);
lean_ctor_set(v_reuseFailAlloc_782_, 9, v_newDecls_755_);
v___x_763_ = v_reuseFailAlloc_782_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_mctx_766_; lean_object* v_zetaDeltaFVarIds_767_; lean_object* v_postponed_768_; lean_object* v_diag_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_780_; 
v___x_764_ = lean_st_ref_set(v___y_743_, v___x_763_);
v___x_765_ = lean_st_ref_take(v___y_742_);
v_mctx_766_ = lean_ctor_get(v___x_765_, 0);
v_zetaDeltaFVarIds_767_ = lean_ctor_get(v___x_765_, 2);
v_postponed_768_ = lean_ctor_get(v___x_765_, 3);
v_diag_769_ = lean_ctor_get(v___x_765_, 4);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_765_, 1);
lean_dec(v_unused_781_);
v___x_771_ = v___x_765_;
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_diag_769_);
lean_inc(v_postponed_768_);
lean_inc(v_zetaDeltaFVarIds_767_);
lean_inc(v_mctx_766_);
lean_dec(v___x_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_780_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_mctx_766_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_zetaDeltaFVarIds_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_postponed_768_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_diag_769_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_st_ref_set(v___y_742_, v___x_775_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref(v_declRanges_741_);
lean_dec(v_declName_740_);
v___x_785_ = lean_box(0);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(lean_object* v_declName_787_, lean_object* v_declRanges_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_787_, v_declRanges_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_declName_793_, lean_object* v_rangeStx_794_, lean_object* v_selectionRangeStx_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_818_; 
v___x_801_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_794_, v___y_798_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
if (lean_obj_tag(v_a_802_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v_a_810_; 
lean_del_object(v___x_804_);
v_val_806_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_val_806_);
lean_dec_ref(v_a_802_);
v___x_807_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_795_, v___y_798_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
if (lean_obj_tag(v_a_808_) == 0)
{
lean_inc(v_val_806_);
v_a_810_ = v_val_806_;
goto v___jp_809_;
}
else
{
lean_object* v_val_813_; 
v_val_813_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v_a_808_);
v_a_810_ = v_val_813_;
goto v___jp_809_;
}
v___jp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_val_806_);
lean_ctor_set(v___x_811_, 1, v_a_810_);
v___x_812_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_793_, v___x_811_, v___y_797_, v___y_799_);
return v___x_812_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_a_802_);
lean_dec(v_declName_793_);
v___x_814_ = lean_box(0);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_814_);
v___x_816_ = v___x_804_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_declName_819_, lean_object* v_rangeStx_820_, lean_object* v_selectionRangeStx_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_declName_819_, v_rangeStx_820_, v_selectionRangeStx_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v_selectionRangeStx_821_);
lean_dec(v_rangeStx_820_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
if (lean_obj_tag(v_a_828_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = l_List_reverse___redArg(v_a_829_);
return v___x_830_;
}
else
{
lean_object* v_head_831_; lean_object* v_tail_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_841_; 
v_head_831_ = lean_ctor_get(v_a_828_, 0);
v_tail_832_ = lean_ctor_get(v_a_828_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_841_ == 0)
{
v___x_834_ = v_a_828_;
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_tail_832_);
lean_inc(v_head_831_);
lean_dec(v_a_828_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_mkLevelParam(v_head_831_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v_a_829_);
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_829_);
v___x_838_ = v_reuseFailAlloc_840_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
v_a_828_ = v_tail_832_;
v_a_829_ = v___x_838_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(lean_object* v_env_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_nextMacroScope_847_; lean_object* v_ngen_848_; lean_object* v_auxDeclNGen_849_; lean_object* v_traceState_850_; lean_object* v_messages_851_; lean_object* v_infoState_852_; lean_object* v_snapshotTasks_853_; lean_object* v_newDecls_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_880_; 
v___x_846_ = lean_st_ref_take(v___y_844_);
v_nextMacroScope_847_ = lean_ctor_get(v___x_846_, 1);
v_ngen_848_ = lean_ctor_get(v___x_846_, 2);
v_auxDeclNGen_849_ = lean_ctor_get(v___x_846_, 3);
v_traceState_850_ = lean_ctor_get(v___x_846_, 4);
v_messages_851_ = lean_ctor_get(v___x_846_, 6);
v_infoState_852_ = lean_ctor_get(v___x_846_, 7);
v_snapshotTasks_853_ = lean_ctor_get(v___x_846_, 8);
v_newDecls_854_ = lean_ctor_get(v___x_846_, 9);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; 
v_unused_881_ = lean_ctor_get(v___x_846_, 5);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v___x_846_, 0);
lean_dec(v_unused_882_);
v___x_856_ = v___x_846_;
v_isShared_857_ = v_isSharedCheck_880_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_newDecls_854_);
lean_inc(v_snapshotTasks_853_);
lean_inc(v_infoState_852_);
lean_inc(v_messages_851_);
lean_inc(v_traceState_850_);
lean_inc(v_auxDeclNGen_849_);
lean_inc(v_ngen_848_);
lean_inc(v_nextMacroScope_847_);
lean_dec(v___x_846_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_880_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 5, v___x_858_);
lean_ctor_set(v___x_856_, 0, v_env_842_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_env_842_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_847_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_849_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_traceState_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_messages_851_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_infoState_852_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_snapshotTasks_853_);
lean_ctor_set(v_reuseFailAlloc_879_, 9, v_newDecls_854_);
v___x_860_ = v_reuseFailAlloc_879_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v_zetaDeltaFVarIds_864_; lean_object* v_postponed_865_; lean_object* v_diag_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v___x_861_ = lean_st_ref_set(v___y_844_, v___x_860_);
v___x_862_ = lean_st_ref_take(v___y_843_);
v_mctx_863_ = lean_ctor_get(v___x_862_, 0);
v_zetaDeltaFVarIds_864_ = lean_ctor_get(v___x_862_, 2);
v_postponed_865_ = lean_ctor_get(v___x_862_, 3);
v_diag_866_ = lean_ctor_get(v___x_862_, 4);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v___x_862_, 1);
lean_dec(v_unused_878_);
v___x_868_ = v___x_862_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_diag_866_);
lean_inc(v_postponed_865_);
lean_inc(v_zetaDeltaFVarIds_864_);
lean_inc(v_mctx_863_);
lean_dec(v___x_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_mctx_863_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_zetaDeltaFVarIds_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_postponed_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_diag_866_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_st_ref_set(v___y_843_, v___x_872_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(lean_object* v_env_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec(v___y_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(lean_object* v_env_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_env_896_; lean_object* v_a_898_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_895_ = lean_st_ref_get(v___y_893_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref(v_env_896_);
lean_dec(v___x_895_);
v___x_908_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_888_, v___y_891_, v___y_893_);
lean_dec_ref(v___x_908_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
v___x_909_ = lean_apply_5(v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v___x_911_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_896_, v___y_891_, v___y_893_);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_919_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v_a_910_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_910_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_object* v_a_920_; 
v_a_920_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_909_);
v_a_898_ = v_a_920_;
goto v___jp_897_;
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v___x_899_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_896_, v___y_891_, v___y_893_);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_907_);
v___x_901_ = v___x_899_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_dec(v___x_899_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 1);
lean_ctor_set(v___x_901_, 0, v_a_898_);
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(lean_object* v_env_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_921_, v_x_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
v___x_930_ = lean_unsigned_to_nat(16u);
v___x_931_ = lean_mk_array(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_938_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
lean_ctor_set(v___x_939_, 2, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = l_Lean_Level_ofNat(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
v___x_955_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_958_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_959_ = l_Lean_mkConst(v___x_958_, v___x_957_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_box(0);
v___x_961_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_962_ = l_Lean_mkConst(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_box(0);
v___x_968_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_969_ = l_Lean_mkConst(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_976_, lean_object* v_e_977_, lean_object* v_axiomDeclRange_x3f_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; uint8_t v___x_1099_; 
v___x_992_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_977_, v_a_980_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v___x_992_);
v___x_1099_ = l_Lean_Expr_hasFVar(v_a_993_);
if (v___x_1099_ == 0)
{
v___y_1078_ = v_a_979_;
v___y_1079_ = v_a_980_;
v___y_1080_ = v_a_981_;
v___y_1081_ = v_a_982_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v___x_1100_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1101_ = l_Lean_MessageData_ofName(v_tacticName_976_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_indentExpr(v_a_993_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1106_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
v___jp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_987_ = lean_box(0);
v___x_988_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_986_, v___x_987_);
v___x_989_ = l_Lean_mkConst(v___y_985_, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
v___jp_994_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_params_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1074_; 
v___x_999_ = lean_st_ref_get(v___y_998_);
v___x_1000_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_993_);
v___x_1001_ = l_Lean_collectLevelParams(v___x_1000_, v_a_993_);
v_params_1002_ = lean_ctor_get(v___x_1001_, 2);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1075_ = lean_ctor_get(v___x_1001_, 1);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v___x_1001_, 0);
lean_dec(v_unused_1076_);
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1074_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_params_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1074_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_env_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_env_1006_ = lean_ctor_get(v___x_999_, 0);
lean_inc_ref(v_env_1006_);
lean_dec(v___x_999_);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_array_to_list(v_params_1002_);
v___x_1009_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_976_);
v___x_1010_ = l_Lean_Name_append(v___x_1009_, v_tacticName_976_);
v___x_1011_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1010_);
v___x_1012_ = l_Lean_Name_append(v___x_1010_, v___x_1011_);
lean_inc(v_a_993_);
lean_inc(v___x_1008_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1013_, 0, v___x_1012_);
lean_closure_set(v___f_1013_, 1, v___x_1008_);
lean_closure_set(v___f_1013_, 2, v___x_1007_);
lean_closure_set(v___f_1013_, 3, v_tacticName_976_);
lean_closure_set(v___f_1013_, 4, v_a_993_);
v___x_1014_ = l_Lean_Environment_unlockAsync(v_env_1006_);
v___x_1015_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v___x_1014_, v___f_1013_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1065_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1065_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1065_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_unbox(v_a_1016_);
lean_dec(v_a_1016_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_dec(v___x_1010_);
lean_dec(v___x_1008_);
lean_del_object(v___x_1004_);
lean_dec(v_a_993_);
v___x_1021_ = lean_box(1);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1064_; 
lean_del_object(v___x_1018_);
v___x_1025_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1026_ = l_Lean_Name_append(v___x_1010_, v___x_1025_);
v___x_1027_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1026_, v___y_998_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1064_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1064_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1032_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1034_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1035_ = l_Lean_mkApp3(v___x_1032_, v___x_1033_, v_a_993_, v___x_1034_);
lean_inc(v___x_1008_);
lean_inc(v_a_1028_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 2, v___x_1035_);
lean_ctor_set(v___x_1004_, 1, v___x_1008_);
lean_ctor_set(v___x_1004_, 0, v_a_1028_);
v___x_1037_ = v___x_1004_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1028_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = 0;
v___x_1039_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*1, v___x_1038_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1039_);
v___x_1041_ = v___x_1030_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_addDecl(v___x_1041_, v___x_1038_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref(v___x_1042_);
if (lean_obj_tag(v_axiomDeclRange_x3f_978_) == 1)
{
lean_object* v_val_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_val_1043_ = lean_ctor_get(v_axiomDeclRange_x3f_978_, 0);
v___x_1044_ = lean_box(0);
lean_inc(v_a_1028_);
v___x_1045_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_1028_, v_val_1043_, v___x_1044_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_dec_ref(v___x_1045_);
v___y_985_ = v_a_1028_;
v___y_986_ = v___x_1008_;
goto v___jp_984_;
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_a_1028_);
lean_dec(v___x_1008_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
v___y_985_ = v_a_1028_;
v___y_986_ = v___x_1008_;
goto v___jp_984_;
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_a_1028_);
lean_dec(v___x_1008_);
v_a_1054_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1042_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1042_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v___x_1010_);
lean_dec(v___x_1008_);
lean_del_object(v___x_1004_);
lean_dec(v_a_993_);
v_a_1066_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1015_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1015_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
v___jp_1077_:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_Expr_hasMVar(v_a_993_);
if (v___x_1082_ == 0)
{
v___y_995_ = v___y_1078_;
v___y_996_ = v___y_1079_;
v___y_997_ = v___y_1080_;
v___y_998_ = v___y_1081_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v___x_1083_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1084_ = l_Lean_MessageData_ofName(v_tacticName_976_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_indentExpr(v_a_993_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1089_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1116_, lean_object* v_e_1117_, lean_object* v_axiomDeclRange_x3f_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1116_, v_e_1117_, v_axiomDeclRange_x3f_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_axiomDeclRange_x3f_1118_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(lean_object* v_env_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_1125_, v___y_1127_, v___y_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(lean_object* v_env_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(v_env_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_00_u03b1_1139_, lean_object* v_env_1140_, lean_object* v_x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_1140_, v_x_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_env_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(v_00_u03b1_1148_, v_env_1149_, v_x_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(lean_object* v_stx_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1157_, v___y_1160_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(lean_object* v_stx_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_stx_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(lean_object* v_declName_1171_, lean_object* v_declRanges_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1171_, v_declRanges_1172_, v___y_1174_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(lean_object* v_declName_1179_, lean_object* v_declRanges_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_1179_, v_declRanges_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Native(builtin);
}
#ifdef __cplusplus
}
#endif
