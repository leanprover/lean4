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
lean_object* v___x_280_; lean_object* v_auxDeclNGen_281_; lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v___x_284_; lean_object* v_fst_285_; lean_object* v_snd_286_; lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_traceState_291_; lean_object* v_cache_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_304_; 
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
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_287_, 3);
lean_dec(v_unused_305_);
v___x_297_ = v___x_287_;
v_isShared_298_ = v_isSharedCheck_304_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_cache_292_);
lean_inc(v_traceState_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_304_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 3, v_snd_286_);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_env_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_snd_286_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_traceState_291_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_cache_292_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v_snapshotTasks_295_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_st_ref_set(v___y_278_, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_fst_285_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_306_, v___y_307_);
lean_dec(v___y_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_310_, v___y_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_opts_324_, lean_object* v_opt_325_){
_start:
{
lean_object* v_name_326_; lean_object* v_defValue_327_; lean_object* v_map_328_; lean_object* v___x_329_; 
v_name_326_ = lean_ctor_get(v_opt_325_, 0);
v_defValue_327_ = lean_ctor_get(v_opt_325_, 1);
v_map_328_ = lean_ctor_get(v_opts_324_, 0);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_328_, v_name_326_);
if (lean_obj_tag(v___x_329_) == 0)
{
uint8_t v___x_330_; 
v___x_330_ = lean_unbox(v_defValue_327_);
return v___x_330_;
}
else
{
lean_object* v_val_331_; 
v_val_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v___x_329_);
if (lean_obj_tag(v_val_331_) == 1)
{
uint8_t v_v_332_; 
v_v_332_ = lean_ctor_get_uint8(v_val_331_, 0);
lean_dec_ref(v_val_331_);
return v_v_332_;
}
else
{
uint8_t v___x_333_; 
lean_dec(v_val_331_);
v___x_333_ = lean_unbox(v_defValue_327_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_opts_334_, lean_object* v_opt_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v_opts_334_, v_opt_335_);
lean_dec_ref(v_opt_335_);
lean_dec_ref(v_opts_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_338_, lean_object* v_opt_339_){
_start:
{
lean_object* v_name_340_; lean_object* v_defValue_341_; lean_object* v_map_342_; lean_object* v___x_343_; 
v_name_340_ = lean_ctor_get(v_opt_339_, 0);
v_defValue_341_ = lean_ctor_get(v_opt_339_, 1);
v_map_342_ = lean_ctor_get(v_opts_338_, 0);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_342_, v_name_340_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_inc(v_defValue_341_);
return v_defValue_341_;
}
else
{
lean_object* v_val_344_; 
v_val_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_344_);
lean_dec_ref(v___x_343_);
if (lean_obj_tag(v_val_344_) == 3)
{
lean_object* v_v_345_; 
v_v_345_ = lean_ctor_get(v_val_344_, 0);
lean_inc(v_v_345_);
lean_dec_ref(v_val_344_);
return v_v_345_;
}
else
{
lean_dec(v_val_344_);
lean_inc(v_defValue_341_);
return v_defValue_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_346_, lean_object* v_opt_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_346_, v_opt_347_);
lean_dec_ref(v_opt_347_);
lean_dec_ref(v_opts_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_o_352_, lean_object* v_k_353_, uint8_t v_v_354_){
_start:
{
lean_object* v_map_355_; uint8_t v_hasTrace_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_370_; 
v_map_355_ = lean_ctor_get(v_o_352_, 0);
v_hasTrace_356_ = lean_ctor_get_uint8(v_o_352_, sizeof(void*)*1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_o_352_);
if (v_isSharedCheck_370_ == 0)
{
v___x_358_ = v_o_352_;
v_isShared_359_ = v_isSharedCheck_370_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_map_355_);
lean_dec(v_o_352_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_370_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_360_, 0, v_v_354_);
lean_inc(v_k_353_);
v___x_361_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_353_, v___x_360_, v_map_355_);
if (v_hasTrace_356_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_365_; 
v___x_362_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1));
v___x_363_ = l_Lean_Name_isPrefixOf(v___x_362_, v_k_353_);
lean_dec(v_k_353_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_365_ = v___x_358_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_361_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_363_);
return v___x_365_;
}
}
else
{
lean_object* v___x_368_; 
lean_dec(v_k_353_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, sizeof(void*)*1, v_hasTrace_356_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_o_371_, lean_object* v_k_372_, lean_object* v_v_373_){
_start:
{
uint8_t v_v_boxed_374_; lean_object* v_res_375_; 
v_v_boxed_374_ = lean_unbox(v_v_373_);
v_res_375_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_o_371_, v_k_372_, v_v_boxed_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_opts_376_, lean_object* v_opt_377_, uint8_t v_val_378_){
_start:
{
lean_object* v_name_379_; lean_object* v___x_380_; 
v_name_379_ = lean_ctor_get(v_opt_377_, 0);
lean_inc(v_name_379_);
lean_dec_ref(v_opt_377_);
v___x_380_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_opts_376_, v_name_379_, v_val_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_opts_381_, lean_object* v_opt_382_, lean_object* v_val_383_){
_start:
{
uint8_t v_val_boxed_384_; lean_object* v_res_385_; 
v_val_boxed_384_ = lean_unbox(v_val_383_);
v_res_385_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_opts_381_, v_opt_382_, v_val_boxed_384_);
return v_res_385_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_box(0);
v___x_399_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_400_ = l_Lean_mkConst(v___x_399_, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_407_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
lean_ctor_set(v___x_407_, 3, v___x_406_);
lean_ctor_set(v___x_407_, 4, v___x_406_);
lean_ctor_set(v___x_407_, 5, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_tacticName_411_, lean_object* v_a_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___y_419_; lean_object* v___y_420_; uint8_t v___y_421_; lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_699_; 
v___x_430_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_408_, v___y_416_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_699_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_699_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_699_;
goto v_resetjp_432_;
}
v___jp_418_:
{
if (v___y_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref(v___y_419_);
v___x_422_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_423_ = l_Lean_MessageData_ofName(v_tacticName_411_);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Lean_Exception_toMessageData(v___y_420_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_428_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec_ref(v___y_415_);
return v___x_429_;
}
else
{
lean_dec_ref(v___y_420_);
lean_dec_ref(v___y_415_);
lean_dec(v_tacticName_411_);
return v___y_419_;
}
}
v_resetjp_432_:
{
lean_object* v___y_436_; lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; lean_object* v___x_461_; lean_object* v_env_462_; lean_object* v_nextMacroScope_463_; lean_object* v_ngen_464_; lean_object* v_auxDeclNGen_465_; lean_object* v_traceState_466_; lean_object* v_messages_467_; lean_object* v_infoState_468_; lean_object* v_snapshotTasks_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_697_; 
v___x_461_ = lean_st_ref_take(v___y_416_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
v_nextMacroScope_463_ = lean_ctor_get(v___x_461_, 1);
v_ngen_464_ = lean_ctor_get(v___x_461_, 2);
v_auxDeclNGen_465_ = lean_ctor_get(v___x_461_, 3);
v_traceState_466_ = lean_ctor_get(v___x_461_, 4);
v_messages_467_ = lean_ctor_get(v___x_461_, 6);
v_infoState_468_ = lean_ctor_get(v___x_461_, 7);
v_snapshotTasks_469_ = lean_ctor_get(v___x_461_, 8);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_461_, 5);
lean_dec(v_unused_698_);
v___x_471_ = v___x_461_;
v_isShared_472_ = v_isSharedCheck_697_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snapshotTasks_469_);
lean_inc(v_infoState_468_);
lean_inc(v_messages_467_);
lean_inc(v_traceState_466_);
lean_inc(v_auxDeclNGen_465_);
lean_inc(v_ngen_464_);
lean_inc(v_nextMacroScope_463_);
lean_inc(v_env_462_);
lean_dec(v___x_461_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_697_;
goto v_resetjp_470_;
}
v___jp_435_:
{
if (lean_obj_tag(v___y_436_) == 0)
{
lean_object* v___x_437_; 
lean_dec_ref(v___y_436_);
v___x_437_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_a_431_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_dec_ref(v___y_415_);
lean_dec(v_tacticName_411_);
return v___x_437_;
}
else
{
lean_object* v_a_438_; uint8_t v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
v___x_439_ = l_Lean_Exception_isInterrupt(v_a_438_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
lean_inc(v_a_438_);
v___x_440_ = l_Lean_Exception_isRuntime(v_a_438_);
v___y_419_ = v___x_437_;
v___y_420_ = v_a_438_;
v___y_421_ = v___x_440_;
goto v___jp_418_;
}
else
{
v___y_419_ = v___x_437_;
v___y_420_ = v_a_438_;
v___y_421_ = v___x_439_;
goto v___jp_418_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_a_431_);
lean_dec_ref(v___y_415_);
lean_dec(v_tacticName_411_);
v_a_441_ = lean_ctor_get(v___y_436_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___y_436_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___y_436_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___y_436_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
v___jp_449_:
{
if (v___y_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v___y_451_);
v___x_453_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_411_);
v___x_454_ = l_Lean_MessageData_ofName(v_tacticName_411_);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_Exception_toMessageData(v___y_450_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_459_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
v___y_436_ = v___x_460_;
goto v___jp_435_;
}
else
{
lean_dec_ref(v___y_450_);
v___y_436_ = v___y_451_;
goto v___jp_435_;
}
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_473_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_431_, 3);
v___x_474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_474_, 0, v_a_431_);
lean_ctor_set(v___x_474_, 1, v___x_409_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v_a_431_);
lean_ctor_set(v___x_475_, 1, v___x_410_);
v___x_476_ = l_Lean_markMeta(v_env_462_, v_a_431_);
v___x_477_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 5, v___x_477_);
lean_ctor_set(v___x_471_, 0, v___x_476_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_nextMacroScope_463_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_ngen_464_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_auxDeclNGen_465_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_traceState_466_);
lean_ctor_set(v_reuseFailAlloc_696_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_696_, 6, v_messages_467_);
lean_ctor_set(v_reuseFailAlloc_696_, 7, v_infoState_468_);
lean_ctor_set(v_reuseFailAlloc_696_, 8, v_snapshotTasks_469_);
v___x_479_ = v_reuseFailAlloc_696_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_zetaDeltaFVarIds_483_; lean_object* v_postponed_484_; lean_object* v_diag_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_694_; 
v___x_480_ = lean_st_ref_set(v___y_416_, v___x_479_);
v___x_481_ = lean_st_ref_take(v___y_414_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
v_zetaDeltaFVarIds_483_ = lean_ctor_get(v___x_481_, 2);
v_postponed_484_ = lean_ctor_get(v___x_481_, 3);
v_diag_485_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_481_, 1);
lean_dec(v_unused_695_);
v___x_487_ = v___x_481_;
v_isShared_488_ = v_isSharedCheck_694_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_diag_485_);
lean_inc(v_postponed_484_);
lean_inc(v_zetaDeltaFVarIds_483_);
lean_inc(v_mctx_482_);
lean_dec(v___x_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_694_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_mctx_482_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_zetaDeltaFVarIds_483_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_postponed_484_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_diag_485_);
v___x_491_ = v_reuseFailAlloc_693_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_options_494_; lean_object* v_env_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_492_ = lean_st_ref_set(v___y_414_, v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_416_);
v_options_494_ = lean_ctor_get(v___y_415_, 2);
v_env_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_env_495_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(1);
v___x_497_ = 1;
v___x_498_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_498_, 0, v___x_474_);
lean_ctor_set(v___x_498_, 1, v_a_412_);
lean_ctor_set(v___x_498_, 2, v___x_496_);
lean_ctor_set(v___x_498_, 3, v___x_475_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*4, v___x_497_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 1);
lean_ctor_set(v___x_433_, 0, v___x_498_);
v___x_500_ = v___x_433_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_692_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
uint8_t v___x_501_; uint8_t v___x_502_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___y_506_; lean_object* v_fileName_507_; lean_object* v_fileMap_508_; lean_object* v_currRecDepth_509_; lean_object* v_ref_510_; lean_object* v_currNamespace_511_; lean_object* v_openDecls_512_; lean_object* v_initHeartbeats_513_; lean_object* v_maxHeartbeats_514_; lean_object* v_quotContext_515_; lean_object* v_currMacroScope_516_; lean_object* v_cancelTk_x3f_517_; uint8_t v_suppressElabErrors_518_; lean_object* v_inheritedTraceOptions_519_; lean_object* v___y_520_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_547_; uint8_t v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___y_576_; lean_object* v___y_577_; uint8_t v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; uint8_t v___y_616_; uint8_t v___x_636_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_671_; uint8_t v___x_691_; 
v___x_501_ = 1;
v___x_502_ = 0;
v___x_572_ = l_Lean_Elab_async;
lean_inc_ref(v_options_494_);
v___x_573_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_options_494_, v___x_572_, v___x_502_);
v___x_574_ = l_Lean_diagnostics;
v___x_636_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_573_, v___x_574_);
v___x_691_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_495_);
lean_dec_ref(v_env_495_);
if (v___x_691_ == 0)
{
if (v___x_636_ == 0)
{
lean_inc_ref(v___y_415_);
v___y_638_ = v___y_415_;
v___y_639_ = v___y_416_;
goto v___jp_637_;
}
else
{
v___y_671_ = v___x_691_;
goto v___jp_670_;
}
}
else
{
v___y_671_ = v___x_636_;
goto v___jp_670_;
}
v___jp_503_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_504_, v___y_506_);
v___x_522_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_522_, 0, v_fileName_507_);
lean_ctor_set(v___x_522_, 1, v_fileMap_508_);
lean_ctor_set(v___x_522_, 2, v___y_504_);
lean_ctor_set(v___x_522_, 3, v_currRecDepth_509_);
lean_ctor_set(v___x_522_, 4, v___x_521_);
lean_ctor_set(v___x_522_, 5, v_ref_510_);
lean_ctor_set(v___x_522_, 6, v_currNamespace_511_);
lean_ctor_set(v___x_522_, 7, v_openDecls_512_);
lean_ctor_set(v___x_522_, 8, v_initHeartbeats_513_);
lean_ctor_set(v___x_522_, 9, v_maxHeartbeats_514_);
lean_ctor_set(v___x_522_, 10, v_quotContext_515_);
lean_ctor_set(v___x_522_, 11, v_currMacroScope_516_);
lean_ctor_set(v___x_522_, 12, v_cancelTk_x3f_517_);
lean_ctor_set(v___x_522_, 13, v_inheritedTraceOptions_519_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*14, v___y_505_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*14 + 1, v_suppressElabErrors_518_);
v___x_523_ = l_Lean_addAndCompile(v___x_500_, v___x_501_, v___x_502_, v___x_522_, v___y_520_);
lean_dec_ref(v___x_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
v___y_436_ = v___x_523_;
goto v___jp_435_;
}
else
{
lean_object* v_a_524_; uint8_t v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
v___x_525_ = l_Lean_Exception_isInterrupt(v_a_524_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
lean_inc(v_a_524_);
v___x_526_ = l_Lean_Exception_isRuntime(v_a_524_);
v___y_450_ = v_a_524_;
v___y_451_ = v___x_523_;
v___y_452_ = v___x_526_;
goto v___jp_449_;
}
else
{
v___y_450_ = v_a_524_;
v___y_451_ = v___x_523_;
v___y_452_ = v___x_525_;
goto v___jp_449_;
}
}
}
v___jp_527_:
{
lean_object* v_fileName_533_; lean_object* v_fileMap_534_; lean_object* v_currRecDepth_535_; lean_object* v_ref_536_; lean_object* v_currNamespace_537_; lean_object* v_openDecls_538_; lean_object* v_initHeartbeats_539_; lean_object* v_maxHeartbeats_540_; lean_object* v_quotContext_541_; lean_object* v_currMacroScope_542_; lean_object* v_cancelTk_x3f_543_; uint8_t v_suppressElabErrors_544_; lean_object* v_inheritedTraceOptions_545_; 
v_fileName_533_ = lean_ctor_get(v___y_531_, 0);
lean_inc_ref(v_fileName_533_);
v_fileMap_534_ = lean_ctor_get(v___y_531_, 1);
lean_inc_ref(v_fileMap_534_);
v_currRecDepth_535_ = lean_ctor_get(v___y_531_, 3);
lean_inc(v_currRecDepth_535_);
v_ref_536_ = lean_ctor_get(v___y_531_, 5);
lean_inc(v_ref_536_);
v_currNamespace_537_ = lean_ctor_get(v___y_531_, 6);
lean_inc(v_currNamespace_537_);
v_openDecls_538_ = lean_ctor_get(v___y_531_, 7);
lean_inc(v_openDecls_538_);
v_initHeartbeats_539_ = lean_ctor_get(v___y_531_, 8);
lean_inc(v_initHeartbeats_539_);
v_maxHeartbeats_540_ = lean_ctor_get(v___y_531_, 9);
lean_inc(v_maxHeartbeats_540_);
v_quotContext_541_ = lean_ctor_get(v___y_531_, 10);
lean_inc(v_quotContext_541_);
v_currMacroScope_542_ = lean_ctor_get(v___y_531_, 11);
lean_inc(v_currMacroScope_542_);
v_cancelTk_x3f_543_ = lean_ctor_get(v___y_531_, 12);
lean_inc(v_cancelTk_x3f_543_);
v_suppressElabErrors_544_ = lean_ctor_get_uint8(v___y_531_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_545_ = lean_ctor_get(v___y_531_, 13);
lean_inc_ref(v_inheritedTraceOptions_545_);
lean_dec_ref(v___y_531_);
v___y_504_ = v___y_528_;
v___y_505_ = v___y_529_;
v___y_506_ = v___y_530_;
v_fileName_507_ = v_fileName_533_;
v_fileMap_508_ = v_fileMap_534_;
v_currRecDepth_509_ = v_currRecDepth_535_;
v_ref_510_ = v_ref_536_;
v_currNamespace_511_ = v_currNamespace_537_;
v_openDecls_512_ = v_openDecls_538_;
v_initHeartbeats_513_ = v_initHeartbeats_539_;
v_maxHeartbeats_514_ = v_maxHeartbeats_540_;
v_quotContext_515_ = v_quotContext_541_;
v_currMacroScope_516_ = v_currMacroScope_542_;
v_cancelTk_x3f_517_ = v_cancelTk_x3f_543_;
v_suppressElabErrors_518_ = v_suppressElabErrors_544_;
v_inheritedTraceOptions_519_ = v_inheritedTraceOptions_545_;
v___y_520_ = v___y_532_;
goto v___jp_503_;
}
v___jp_546_:
{
if (v___y_552_ == 0)
{
lean_object* v___x_553_; lean_object* v_env_554_; lean_object* v_nextMacroScope_555_; lean_object* v_ngen_556_; lean_object* v_auxDeclNGen_557_; lean_object* v_traceState_558_; lean_object* v_messages_559_; lean_object* v_infoState_560_; lean_object* v_snapshotTasks_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
v___x_553_ = lean_st_ref_take(v___y_550_);
v_env_554_ = lean_ctor_get(v___x_553_, 0);
v_nextMacroScope_555_ = lean_ctor_get(v___x_553_, 1);
v_ngen_556_ = lean_ctor_get(v___x_553_, 2);
v_auxDeclNGen_557_ = lean_ctor_get(v___x_553_, 3);
v_traceState_558_ = lean_ctor_get(v___x_553_, 4);
v_messages_559_ = lean_ctor_get(v___x_553_, 6);
v_infoState_560_ = lean_ctor_get(v___x_553_, 7);
v_snapshotTasks_561_ = lean_ctor_get(v___x_553_, 8);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v___x_553_, 5);
lean_dec(v_unused_571_);
v___x_563_ = v___x_553_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snapshotTasks_561_);
lean_inc(v_infoState_560_);
lean_inc(v_messages_559_);
lean_inc(v_traceState_558_);
lean_inc(v_auxDeclNGen_557_);
lean_inc(v_ngen_556_);
lean_inc(v_nextMacroScope_555_);
lean_inc(v_env_554_);
lean_dec(v___x_553_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_Kernel_enableDiag(v_env_554_, v___y_548_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 5, v___x_477_);
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_nextMacroScope_555_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_ngen_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_auxDeclNGen_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_traceState_558_);
lean_ctor_set(v_reuseFailAlloc_569_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_569_, 6, v_messages_559_);
lean_ctor_set(v_reuseFailAlloc_569_, 7, v_infoState_560_);
lean_ctor_set(v_reuseFailAlloc_569_, 8, v_snapshotTasks_561_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_st_ref_set(v___y_550_, v___x_567_);
v___y_528_ = v___y_547_;
v___y_529_ = v___y_548_;
v___y_530_ = v___y_551_;
v___y_531_ = v___y_549_;
v___y_532_ = v___y_550_;
goto v___jp_527_;
}
}
}
else
{
v___y_528_ = v___y_547_;
v___y_529_ = v___y_548_;
v___y_530_ = v___y_551_;
v___y_531_ = v___y_549_;
v___y_532_ = v___y_550_;
goto v___jp_527_;
}
}
v___jp_575_:
{
lean_object* v___x_581_; lean_object* v_fileName_582_; lean_object* v_fileMap_583_; lean_object* v_currRecDepth_584_; lean_object* v_ref_585_; lean_object* v_currNamespace_586_; lean_object* v_openDecls_587_; lean_object* v_initHeartbeats_588_; lean_object* v_maxHeartbeats_589_; lean_object* v_quotContext_590_; lean_object* v_currMacroScope_591_; lean_object* v_cancelTk_x3f_592_; uint8_t v_suppressElabErrors_593_; lean_object* v_inheritedTraceOptions_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_607_; 
v___x_581_ = lean_st_ref_get(v___y_580_);
v_fileName_582_ = lean_ctor_get(v___y_579_, 0);
v_fileMap_583_ = lean_ctor_get(v___y_579_, 1);
v_currRecDepth_584_ = lean_ctor_get(v___y_579_, 3);
v_ref_585_ = lean_ctor_get(v___y_579_, 5);
v_currNamespace_586_ = lean_ctor_get(v___y_579_, 6);
v_openDecls_587_ = lean_ctor_get(v___y_579_, 7);
v_initHeartbeats_588_ = lean_ctor_get(v___y_579_, 8);
v_maxHeartbeats_589_ = lean_ctor_get(v___y_579_, 9);
v_quotContext_590_ = lean_ctor_get(v___y_579_, 10);
v_currMacroScope_591_ = lean_ctor_get(v___y_579_, 11);
v_cancelTk_x3f_592_ = lean_ctor_get(v___y_579_, 12);
v_suppressElabErrors_593_ = lean_ctor_get_uint8(v___y_579_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_594_ = lean_ctor_get(v___y_579_, 13);
v_isSharedCheck_607_ = !lean_is_exclusive(v___y_579_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; lean_object* v_unused_609_; 
v_unused_608_ = lean_ctor_get(v___y_579_, 4);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v___y_579_, 2);
lean_dec(v_unused_609_);
v___x_596_ = v___y_579_;
v_isShared_597_ = v_isSharedCheck_607_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_inheritedTraceOptions_594_);
lean_inc(v_cancelTk_x3f_592_);
lean_inc(v_currMacroScope_591_);
lean_inc(v_quotContext_590_);
lean_inc(v_maxHeartbeats_589_);
lean_inc(v_initHeartbeats_588_);
lean_inc(v_openDecls_587_);
lean_inc(v_currNamespace_586_);
lean_inc(v_ref_585_);
lean_inc(v_currRecDepth_584_);
lean_inc(v_fileMap_583_);
lean_inc(v_fileName_582_);
lean_dec(v___y_579_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_607_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_env_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v_env_598_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_581_);
v___x_599_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_576_, v___y_577_);
lean_inc_ref(v_inheritedTraceOptions_594_);
lean_inc(v_cancelTk_x3f_592_);
lean_inc(v_currMacroScope_591_);
lean_inc(v_quotContext_590_);
lean_inc(v_maxHeartbeats_589_);
lean_inc(v_initHeartbeats_588_);
lean_inc(v_openDecls_587_);
lean_inc(v_currNamespace_586_);
lean_inc(v_ref_585_);
lean_inc(v_currRecDepth_584_);
lean_inc_ref(v___y_576_);
lean_inc_ref(v_fileMap_583_);
lean_inc_ref(v_fileName_582_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 4, v___x_599_);
lean_ctor_set(v___x_596_, 2, v___y_576_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_fileName_582_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_fileMap_583_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v___y_576_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_currRecDepth_584_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_606_, 5, v_ref_585_);
lean_ctor_set(v_reuseFailAlloc_606_, 6, v_currNamespace_586_);
lean_ctor_set(v_reuseFailAlloc_606_, 7, v_openDecls_587_);
lean_ctor_set(v_reuseFailAlloc_606_, 8, v_initHeartbeats_588_);
lean_ctor_set(v_reuseFailAlloc_606_, 9, v_maxHeartbeats_589_);
lean_ctor_set(v_reuseFailAlloc_606_, 10, v_quotContext_590_);
lean_ctor_set(v_reuseFailAlloc_606_, 11, v_currMacroScope_591_);
lean_ctor_set(v_reuseFailAlloc_606_, 12, v_cancelTk_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_606_, 13, v_inheritedTraceOptions_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*14 + 1, v_suppressElabErrors_593_);
v___x_601_ = v_reuseFailAlloc_606_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; 
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*14, v___y_578_);
v___x_602_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_603_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___y_576_, v___x_602_, v___x_501_);
v___x_604_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_603_, v___x_574_);
v___x_605_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_598_);
lean_dec_ref(v_env_598_);
if (v___x_605_ == 0)
{
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_601_);
v___y_504_ = v___x_603_;
v___y_505_ = v___x_604_;
v___y_506_ = v___y_577_;
v_fileName_507_ = v_fileName_582_;
v_fileMap_508_ = v_fileMap_583_;
v_currRecDepth_509_ = v_currRecDepth_584_;
v_ref_510_ = v_ref_585_;
v_currNamespace_511_ = v_currNamespace_586_;
v_openDecls_512_ = v_openDecls_587_;
v_initHeartbeats_513_ = v_initHeartbeats_588_;
v_maxHeartbeats_514_ = v_maxHeartbeats_589_;
v_quotContext_515_ = v_quotContext_590_;
v_currMacroScope_516_ = v_currMacroScope_591_;
v_cancelTk_x3f_517_ = v_cancelTk_x3f_592_;
v_suppressElabErrors_518_ = v_suppressElabErrors_593_;
v_inheritedTraceOptions_519_ = v_inheritedTraceOptions_594_;
v___y_520_ = v___y_580_;
goto v___jp_503_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_594_);
lean_dec(v_cancelTk_x3f_592_);
lean_dec(v_currMacroScope_591_);
lean_dec(v_quotContext_590_);
lean_dec(v_maxHeartbeats_589_);
lean_dec(v_initHeartbeats_588_);
lean_dec(v_openDecls_587_);
lean_dec(v_currNamespace_586_);
lean_dec(v_ref_585_);
lean_dec(v_currRecDepth_584_);
lean_dec_ref(v_fileMap_583_);
lean_dec_ref(v_fileName_582_);
v___y_547_ = v___x_603_;
v___y_548_ = v___x_604_;
v___y_549_ = v___x_601_;
v___y_550_ = v___y_580_;
v___y_551_ = v___y_577_;
v___y_552_ = v___x_605_;
goto v___jp_546_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_594_);
lean_dec(v_cancelTk_x3f_592_);
lean_dec(v_currMacroScope_591_);
lean_dec(v_quotContext_590_);
lean_dec(v_maxHeartbeats_589_);
lean_dec(v_initHeartbeats_588_);
lean_dec(v_openDecls_587_);
lean_dec(v_currNamespace_586_);
lean_dec(v_ref_585_);
lean_dec(v_currRecDepth_584_);
lean_dec_ref(v_fileMap_583_);
lean_dec_ref(v_fileName_582_);
v___y_547_ = v___x_603_;
v___y_548_ = v___x_604_;
v___y_549_ = v___x_601_;
v___y_550_ = v___y_580_;
v___y_551_ = v___y_577_;
v___y_552_ = v___x_604_;
goto v___jp_546_;
}
}
}
}
v___jp_610_:
{
if (v___y_616_ == 0)
{
lean_object* v___x_617_; lean_object* v_env_618_; lean_object* v_nextMacroScope_619_; lean_object* v_ngen_620_; lean_object* v_auxDeclNGen_621_; lean_object* v_traceState_622_; lean_object* v_messages_623_; lean_object* v_infoState_624_; lean_object* v_snapshotTasks_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_634_; 
v___x_617_ = lean_st_ref_take(v___y_614_);
v_env_618_ = lean_ctor_get(v___x_617_, 0);
v_nextMacroScope_619_ = lean_ctor_get(v___x_617_, 1);
v_ngen_620_ = lean_ctor_get(v___x_617_, 2);
v_auxDeclNGen_621_ = lean_ctor_get(v___x_617_, 3);
v_traceState_622_ = lean_ctor_get(v___x_617_, 4);
v_messages_623_ = lean_ctor_get(v___x_617_, 6);
v_infoState_624_ = lean_ctor_get(v___x_617_, 7);
v_snapshotTasks_625_ = lean_ctor_get(v___x_617_, 8);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v___x_617_, 5);
lean_dec(v_unused_635_);
v___x_627_ = v___x_617_;
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snapshotTasks_625_);
lean_inc(v_infoState_624_);
lean_inc(v_messages_623_);
lean_inc(v_traceState_622_);
lean_inc(v_auxDeclNGen_621_);
lean_inc(v_ngen_620_);
lean_inc(v_nextMacroScope_619_);
lean_inc(v_env_618_);
lean_dec(v___x_617_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_Kernel_enableDiag(v_env_618_, v___y_615_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 5, v___x_477_);
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_nextMacroScope_619_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_ngen_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_auxDeclNGen_621_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_traceState_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_633_, 6, v_messages_623_);
lean_ctor_set(v_reuseFailAlloc_633_, 7, v_infoState_624_);
lean_ctor_set(v_reuseFailAlloc_633_, 8, v_snapshotTasks_625_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; 
v___x_632_ = lean_st_ref_set(v___y_614_, v___x_631_);
v___y_576_ = v___y_611_;
v___y_577_ = v___y_613_;
v___y_578_ = v___y_615_;
v___y_579_ = v___y_612_;
v___y_580_ = v___y_614_;
goto v___jp_575_;
}
}
}
else
{
v___y_576_ = v___y_611_;
v___y_577_ = v___y_613_;
v___y_578_ = v___y_615_;
v___y_579_ = v___y_612_;
v___y_580_ = v___y_614_;
goto v___jp_575_;
}
}
v___jp_637_:
{
lean_object* v___x_640_; lean_object* v_fileName_641_; lean_object* v_fileMap_642_; lean_object* v_currRecDepth_643_; lean_object* v_ref_644_; lean_object* v_currNamespace_645_; lean_object* v_openDecls_646_; lean_object* v_initHeartbeats_647_; lean_object* v_maxHeartbeats_648_; lean_object* v_quotContext_649_; lean_object* v_currMacroScope_650_; lean_object* v_cancelTk_x3f_651_; uint8_t v_suppressElabErrors_652_; lean_object* v_inheritedTraceOptions_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_667_; 
v___x_640_ = lean_st_ref_get(v___y_639_);
v_fileName_641_ = lean_ctor_get(v___y_638_, 0);
v_fileMap_642_ = lean_ctor_get(v___y_638_, 1);
v_currRecDepth_643_ = lean_ctor_get(v___y_638_, 3);
v_ref_644_ = lean_ctor_get(v___y_638_, 5);
v_currNamespace_645_ = lean_ctor_get(v___y_638_, 6);
v_openDecls_646_ = lean_ctor_get(v___y_638_, 7);
v_initHeartbeats_647_ = lean_ctor_get(v___y_638_, 8);
v_maxHeartbeats_648_ = lean_ctor_get(v___y_638_, 9);
v_quotContext_649_ = lean_ctor_get(v___y_638_, 10);
v_currMacroScope_650_ = lean_ctor_get(v___y_638_, 11);
v_cancelTk_x3f_651_ = lean_ctor_get(v___y_638_, 12);
v_suppressElabErrors_652_ = lean_ctor_get_uint8(v___y_638_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_653_ = lean_ctor_get(v___y_638_, 13);
v_isSharedCheck_667_ = !lean_is_exclusive(v___y_638_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_668_ = lean_ctor_get(v___y_638_, 4);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v___y_638_, 2);
lean_dec(v_unused_669_);
v___x_655_ = v___y_638_;
v_isShared_656_ = v_isSharedCheck_667_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_inheritedTraceOptions_653_);
lean_inc(v_cancelTk_x3f_651_);
lean_inc(v_currMacroScope_650_);
lean_inc(v_quotContext_649_);
lean_inc(v_maxHeartbeats_648_);
lean_inc(v_initHeartbeats_647_);
lean_inc(v_openDecls_646_);
lean_inc(v_currNamespace_645_);
lean_inc(v_ref_644_);
lean_inc(v_currRecDepth_643_);
lean_inc(v_fileMap_642_);
lean_inc(v_fileName_641_);
lean_dec(v___y_638_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_667_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_env_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v_env_657_ = lean_ctor_get(v___x_640_, 0);
lean_inc_ref(v_env_657_);
lean_dec(v___x_640_);
v___x_658_ = l_Lean_maxRecDepth;
v___x_659_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_573_, v___x_658_);
lean_inc_ref(v___x_573_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v___x_659_);
lean_ctor_set(v___x_655_, 2, v___x_573_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_fileName_641_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_fileMap_642_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v_currRecDepth_643_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_666_, 5, v_ref_644_);
lean_ctor_set(v_reuseFailAlloc_666_, 6, v_currNamespace_645_);
lean_ctor_set(v_reuseFailAlloc_666_, 7, v_openDecls_646_);
lean_ctor_set(v_reuseFailAlloc_666_, 8, v_initHeartbeats_647_);
lean_ctor_set(v_reuseFailAlloc_666_, 9, v_maxHeartbeats_648_);
lean_ctor_set(v_reuseFailAlloc_666_, 10, v_quotContext_649_);
lean_ctor_set(v_reuseFailAlloc_666_, 11, v_currMacroScope_650_);
lean_ctor_set(v_reuseFailAlloc_666_, 12, v_cancelTk_x3f_651_);
lean_ctor_set(v_reuseFailAlloc_666_, 13, v_inheritedTraceOptions_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*14 + 1, v_suppressElabErrors_652_);
v___x_661_ = v_reuseFailAlloc_666_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; uint8_t v___x_665_; 
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*14, v___x_636_);
v___x_662_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_663_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___x_573_, v___x_662_, v___x_502_);
v___x_664_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_663_, v___x_574_);
v___x_665_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_657_);
lean_dec_ref(v_env_657_);
if (v___x_665_ == 0)
{
if (v___x_664_ == 0)
{
v___y_576_ = v___x_663_;
v___y_577_ = v___x_658_;
v___y_578_ = v___x_664_;
v___y_579_ = v___x_661_;
v___y_580_ = v___y_639_;
goto v___jp_575_;
}
else
{
v___y_611_ = v___x_663_;
v___y_612_ = v___x_661_;
v___y_613_ = v___x_658_;
v___y_614_ = v___y_639_;
v___y_615_ = v___x_664_;
v___y_616_ = v___x_665_;
goto v___jp_610_;
}
}
else
{
v___y_611_ = v___x_663_;
v___y_612_ = v___x_661_;
v___y_613_ = v___x_658_;
v___y_614_ = v___y_639_;
v___y_615_ = v___x_664_;
v___y_616_ = v___x_664_;
goto v___jp_610_;
}
}
}
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
lean_object* v___x_672_; lean_object* v_env_673_; lean_object* v_nextMacroScope_674_; lean_object* v_ngen_675_; lean_object* v_auxDeclNGen_676_; lean_object* v_traceState_677_; lean_object* v_messages_678_; lean_object* v_infoState_679_; lean_object* v_snapshotTasks_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v___x_672_ = lean_st_ref_take(v___y_416_);
v_env_673_ = lean_ctor_get(v___x_672_, 0);
v_nextMacroScope_674_ = lean_ctor_get(v___x_672_, 1);
v_ngen_675_ = lean_ctor_get(v___x_672_, 2);
v_auxDeclNGen_676_ = lean_ctor_get(v___x_672_, 3);
v_traceState_677_ = lean_ctor_get(v___x_672_, 4);
v_messages_678_ = lean_ctor_get(v___x_672_, 6);
v_infoState_679_ = lean_ctor_get(v___x_672_, 7);
v_snapshotTasks_680_ = lean_ctor_get(v___x_672_, 8);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_672_, 5);
lean_dec(v_unused_690_);
v___x_682_ = v___x_672_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_snapshotTasks_680_);
lean_inc(v_infoState_679_);
lean_inc(v_messages_678_);
lean_inc(v_traceState_677_);
lean_inc(v_auxDeclNGen_676_);
lean_inc(v_ngen_675_);
lean_inc(v_nextMacroScope_674_);
lean_inc(v_env_673_);
lean_dec(v___x_672_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_Kernel_enableDiag(v_env_673_, v___x_636_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 5, v___x_477_);
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_nextMacroScope_674_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_ngen_675_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_auxDeclNGen_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_traceState_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_688_, 6, v_messages_678_);
lean_ctor_set(v_reuseFailAlloc_688_, 7, v_infoState_679_);
lean_ctor_set(v_reuseFailAlloc_688_, 8, v_snapshotTasks_680_);
v___x_686_ = v_reuseFailAlloc_688_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; 
v___x_687_ = lean_st_ref_set(v___y_416_, v___x_686_);
lean_inc_ref(v___y_415_);
v___y_638_ = v___y_415_;
v___y_639_ = v___y_416_;
goto v___jp_637_;
}
}
}
else
{
lean_inc_ref(v___y_415_);
v___y_638_ = v___y_415_;
v___y_639_ = v___y_416_;
goto v___jp_637_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v_tacticName_703_, lean_object* v_a_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_700_, v___x_701_, v___x_702_, v_tacticName_703_, v_a_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object* v_stx_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 0;
v___x_715_ = l_Lean_Syntax_getRange_x3f(v_stx_711_, v___x_714_);
if (lean_obj_tag(v___x_715_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_728_; 
v_val_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_728_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_728_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_728_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fileMap_720_; lean_object* v_start_721_; lean_object* v_stop_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_fileMap_720_ = lean_ctor_get(v___y_712_, 1);
v_start_721_ = lean_ctor_get(v_val_716_, 0);
lean_inc(v_start_721_);
v_stop_722_ = lean_ctor_get(v_val_716_, 1);
lean_inc(v_stop_722_);
lean_dec(v_val_716_);
lean_inc_ref(v_fileMap_720_);
v___x_723_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_720_, v_start_721_, v_stop_722_);
lean_dec(v_stop_722_);
lean_dec(v_start_721_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_723_);
v___x_725_ = v___x_718_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v___x_715_);
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object* v_stx_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_731_, v___y_732_);
lean_dec_ref(v___y_732_);
lean_dec(v_stx_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(lean_object* v_declName_735_, lean_object* v_declRanges_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Lean_Name_isAnonymous(v_declName_735_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v_env_742_; lean_object* v_nextMacroScope_743_; lean_object* v_ngen_744_; lean_object* v_auxDeclNGen_745_; lean_object* v_traceState_746_; lean_object* v_messages_747_; lean_object* v_infoState_748_; lean_object* v_snapshotTasks_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_777_; 
v___x_741_ = lean_st_ref_take(v___y_738_);
v_env_742_ = lean_ctor_get(v___x_741_, 0);
v_nextMacroScope_743_ = lean_ctor_get(v___x_741_, 1);
v_ngen_744_ = lean_ctor_get(v___x_741_, 2);
v_auxDeclNGen_745_ = lean_ctor_get(v___x_741_, 3);
v_traceState_746_ = lean_ctor_get(v___x_741_, 4);
v_messages_747_ = lean_ctor_get(v___x_741_, 6);
v_infoState_748_ = lean_ctor_get(v___x_741_, 7);
v_snapshotTasks_749_ = lean_ctor_get(v___x_741_, 8);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_741_, 5);
lean_dec(v_unused_778_);
v___x_751_ = v___x_741_;
v_isShared_752_ = v_isSharedCheck_777_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snapshotTasks_749_);
lean_inc(v_infoState_748_);
lean_inc(v_messages_747_);
lean_inc(v_traceState_746_);
lean_inc(v_auxDeclNGen_745_);
lean_inc(v_ngen_744_);
lean_inc(v_nextMacroScope_743_);
lean_inc(v_env_742_);
lean_dec(v___x_741_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_777_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_753_ = l_Lean_declRangeExt;
v___x_754_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_753_, v_env_742_, v_declName_735_, v_declRanges_736_);
v___x_755_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 5, v___x_755_);
lean_ctor_set(v___x_751_, 0, v___x_754_);
v___x_757_ = v___x_751_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_nextMacroScope_743_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_ngen_744_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_auxDeclNGen_745_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_traceState_746_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_messages_747_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_infoState_748_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v_snapshotTasks_749_);
v___x_757_ = v_reuseFailAlloc_776_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_mctx_760_; lean_object* v_zetaDeltaFVarIds_761_; lean_object* v_postponed_762_; lean_object* v_diag_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_774_; 
v___x_758_ = lean_st_ref_set(v___y_738_, v___x_757_);
v___x_759_ = lean_st_ref_take(v___y_737_);
v_mctx_760_ = lean_ctor_get(v___x_759_, 0);
v_zetaDeltaFVarIds_761_ = lean_ctor_get(v___x_759_, 2);
v_postponed_762_ = lean_ctor_get(v___x_759_, 3);
v_diag_763_ = lean_ctor_get(v___x_759_, 4);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_759_, 1);
lean_dec(v_unused_775_);
v___x_765_ = v___x_759_;
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_diag_763_);
lean_inc(v_postponed_762_);
lean_inc(v_zetaDeltaFVarIds_761_);
lean_inc(v_mctx_760_);
lean_dec(v___x_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_mctx_760_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_zetaDeltaFVarIds_761_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_postponed_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_diag_763_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_st_ref_set(v___y_737_, v___x_769_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_declRanges_736_);
lean_dec(v_declName_735_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(lean_object* v_declName_781_, lean_object* v_declRanges_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_781_, v_declRanges_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_declName_787_, lean_object* v_rangeStx_788_, lean_object* v_selectionRangeStx_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_812_; 
v___x_795_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_788_, v___y_792_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_812_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_812_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_812_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v_a_804_; 
lean_del_object(v___x_798_);
v_val_800_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_800_);
lean_dec_ref(v_a_796_);
v___x_801_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_789_, v___y_792_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
if (lean_obj_tag(v_a_802_) == 0)
{
lean_inc(v_val_800_);
v_a_804_ = v_val_800_;
goto v___jp_803_;
}
else
{
lean_object* v_val_807_; 
v_val_807_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_val_807_);
lean_dec_ref(v_a_802_);
v_a_804_ = v_val_807_;
goto v___jp_803_;
}
v___jp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_val_800_);
lean_ctor_set(v___x_805_, 1, v_a_804_);
v___x_806_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_787_, v___x_805_, v___y_791_, v___y_793_);
return v___x_806_;
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v_a_796_);
lean_dec(v_declName_787_);
v___x_808_ = lean_box(0);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_808_);
v___x_810_ = v___x_798_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_declName_813_, lean_object* v_rangeStx_814_, lean_object* v_selectionRangeStx_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_declName_813_, v_rangeStx_814_, v_selectionRangeStx_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v_selectionRangeStx_815_);
lean_dec(v_rangeStx_814_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
if (lean_obj_tag(v_a_822_) == 0)
{
lean_object* v___x_824_; 
v___x_824_ = l_List_reverse___redArg(v_a_823_);
return v___x_824_;
}
else
{
lean_object* v_head_825_; lean_object* v_tail_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_835_; 
v_head_825_ = lean_ctor_get(v_a_822_, 0);
v_tail_826_ = lean_ctor_get(v_a_822_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_835_ == 0)
{
v___x_828_ = v_a_822_;
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_tail_826_);
lean_inc(v_head_825_);
lean_dec(v_a_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = l_Lean_mkLevelParam(v_head_825_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_a_823_);
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_a_823_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v_a_822_ = v_tail_826_;
v_a_823_ = v___x_832_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(lean_object* v_env_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; lean_object* v_nextMacroScope_841_; lean_object* v_ngen_842_; lean_object* v_auxDeclNGen_843_; lean_object* v_traceState_844_; lean_object* v_messages_845_; lean_object* v_infoState_846_; lean_object* v_snapshotTasks_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_873_; 
v___x_840_ = lean_st_ref_take(v___y_838_);
v_nextMacroScope_841_ = lean_ctor_get(v___x_840_, 1);
v_ngen_842_ = lean_ctor_get(v___x_840_, 2);
v_auxDeclNGen_843_ = lean_ctor_get(v___x_840_, 3);
v_traceState_844_ = lean_ctor_get(v___x_840_, 4);
v_messages_845_ = lean_ctor_get(v___x_840_, 6);
v_infoState_846_ = lean_ctor_get(v___x_840_, 7);
v_snapshotTasks_847_ = lean_ctor_get(v___x_840_, 8);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_874_ = lean_ctor_get(v___x_840_, 5);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_875_);
v___x_849_ = v___x_840_;
v_isShared_850_ = v_isSharedCheck_873_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snapshotTasks_847_);
lean_inc(v_infoState_846_);
lean_inc(v_messages_845_);
lean_inc(v_traceState_844_);
lean_inc(v_auxDeclNGen_843_);
lean_inc(v_ngen_842_);
lean_inc(v_nextMacroScope_841_);
lean_dec(v___x_840_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_873_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 5, v___x_851_);
lean_ctor_set(v___x_849_, 0, v_env_836_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_env_836_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_nextMacroScope_841_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_ngen_842_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_auxDeclNGen_843_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_traceState_844_);
lean_ctor_set(v_reuseFailAlloc_872_, 5, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_872_, 6, v_messages_845_);
lean_ctor_set(v_reuseFailAlloc_872_, 7, v_infoState_846_);
lean_ctor_set(v_reuseFailAlloc_872_, 8, v_snapshotTasks_847_);
v___x_853_ = v_reuseFailAlloc_872_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_mctx_856_; lean_object* v_zetaDeltaFVarIds_857_; lean_object* v_postponed_858_; lean_object* v_diag_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_870_; 
v___x_854_ = lean_st_ref_set(v___y_838_, v___x_853_);
v___x_855_ = lean_st_ref_take(v___y_837_);
v_mctx_856_ = lean_ctor_get(v___x_855_, 0);
v_zetaDeltaFVarIds_857_ = lean_ctor_get(v___x_855_, 2);
v_postponed_858_ = lean_ctor_get(v___x_855_, 3);
v_diag_859_ = lean_ctor_get(v___x_855_, 4);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_855_, 1);
lean_dec(v_unused_871_);
v___x_861_ = v___x_855_;
v_isShared_862_ = v_isSharedCheck_870_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_diag_859_);
lean_inc(v_postponed_858_);
lean_inc(v_zetaDeltaFVarIds_857_);
lean_inc(v_mctx_856_);
lean_dec(v___x_855_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_870_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_mctx_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_zetaDeltaFVarIds_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_postponed_858_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_diag_859_);
v___x_865_ = v_reuseFailAlloc_869_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_st_ref_set(v___y_837_, v___x_865_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(lean_object* v_env_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(lean_object* v_env_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; lean_object* v_env_889_; lean_object* v_a_891_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_888_ = lean_st_ref_get(v___y_886_);
v_env_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_ref(v_env_889_);
lean_dec(v___x_888_);
v___x_901_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_881_, v___y_884_, v___y_886_);
lean_dec_ref(v___x_901_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
v___x_902_ = lean_apply_5(v_x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_889_, v___y_884_, v___y_886_);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_912_);
v___x_906_ = v___x_904_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_dec(v___x_904_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v_a_903_);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_903_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_913_; 
v_a_913_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_913_);
lean_dec_ref(v___x_902_);
v_a_891_ = v_a_913_;
goto v___jp_890_;
}
v___jp_890_:
{
lean_object* v___x_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v___x_892_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_889_, v___y_884_, v___y_886_);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_900_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v_a_891_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_891_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(lean_object* v_env_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v___x_923_ = lean_unsigned_to_nat(16u);
v___x_924_ = lean_mk_array(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_931_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
lean_ctor_set(v___x_932_, 2, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = l_Lean_Level_ofNat(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_box(0);
v___x_948_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_951_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_952_ = l_Lean_mkConst(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_box(0);
v___x_954_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_955_ = l_Lean_mkConst(v___x_954_, v___x_953_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_box(0);
v___x_961_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_962_ = l_Lean_mkConst(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_969_, lean_object* v_e_970_, lean_object* v_axiomDeclRange_x3f_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___x_1092_; 
v___x_985_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_970_, v_a_973_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_1092_ = l_Lean_Expr_hasFVar(v_a_986_);
if (v___x_1092_ == 0)
{
v___y_1071_ = v_a_972_;
v___y_1072_ = v_a_973_;
v___y_1073_ = v_a_974_;
v___y_1074_ = v_a_975_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v___x_1093_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1094_ = l_Lean_MessageData_ofName(v_tacticName_969_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_indentExpr(v_a_986_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1099_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
v___jp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_980_ = lean_box(0);
v___x_981_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_979_, v___x_980_);
v___x_982_ = l_Lean_mkConst(v___y_978_, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
v___jp_987_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_params_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1067_; 
v___x_992_ = lean_st_ref_get(v___y_991_);
v___x_993_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_986_);
v___x_994_ = l_Lean_collectLevelParams(v___x_993_, v_a_986_);
v_params_995_ = lean_ctor_get(v___x_994_, 2);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1068_ = lean_ctor_get(v___x_994_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v___x_994_, 0);
lean_dec(v_unused_1069_);
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1067_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_params_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1067_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_env_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_env_999_ = lean_ctor_get(v___x_992_, 0);
lean_inc_ref(v_env_999_);
lean_dec(v___x_992_);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_array_to_list(v_params_995_);
v___x_1002_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_969_);
v___x_1003_ = l_Lean_Name_append(v___x_1002_, v_tacticName_969_);
v___x_1004_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1003_);
v___x_1005_ = l_Lean_Name_append(v___x_1003_, v___x_1004_);
lean_inc(v_a_986_);
lean_inc(v___x_1001_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1006_, 0, v___x_1005_);
lean_closure_set(v___f_1006_, 1, v___x_1001_);
lean_closure_set(v___f_1006_, 2, v___x_1000_);
lean_closure_set(v___f_1006_, 3, v_tacticName_969_);
lean_closure_set(v___f_1006_, 4, v_a_986_);
v___x_1007_ = l_Lean_Environment_unlockAsync(v_env_999_);
v___x_1008_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v___x_1007_, v___f_1006_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1058_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1058_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1058_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_unbox(v_a_1009_);
lean_dec(v_a_1009_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v___x_1003_);
lean_dec(v___x_1001_);
lean_del_object(v___x_997_);
lean_dec(v_a_986_);
v___x_1014_ = lean_box(1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1057_; 
lean_del_object(v___x_1011_);
v___x_1018_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1019_ = l_Lean_Name_append(v___x_1003_, v___x_1018_);
v___x_1020_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1019_, v___y_991_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1057_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1057_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1025_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1026_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1027_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1028_ = l_Lean_mkApp3(v___x_1025_, v___x_1026_, v_a_986_, v___x_1027_);
lean_inc(v___x_1001_);
lean_inc(v_a_1021_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v___x_1028_);
lean_ctor_set(v___x_997_, 1, v___x_1001_);
lean_ctor_set(v___x_997_, 0, v_a_1021_);
v___x_1030_ = v___x_997_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1021_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = 0;
v___x_1032_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_1031_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1032_);
v___x_1034_ = v___x_1023_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_addDecl(v___x_1034_, v___x_1031_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_dec_ref(v___x_1035_);
if (lean_obj_tag(v_axiomDeclRange_x3f_971_) == 1)
{
lean_object* v_val_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_val_1036_ = lean_ctor_get(v_axiomDeclRange_x3f_971_, 0);
v___x_1037_ = lean_box(0);
lean_inc(v_a_1021_);
v___x_1038_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_1021_, v_val_1036_, v___x_1037_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref(v___x_1038_);
v___y_978_ = v_a_1021_;
v___y_979_ = v___x_1001_;
goto v___jp_977_;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1021_);
lean_dec(v___x_1001_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
v___y_978_ = v_a_1021_;
v___y_979_ = v___x_1001_;
goto v___jp_977_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_1021_);
lean_dec(v___x_1001_);
v_a_1047_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1035_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1035_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
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
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v___x_1003_);
lean_dec(v___x_1001_);
lean_del_object(v___x_997_);
lean_dec(v_a_986_);
v_a_1059_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1008_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1008_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
v___jp_1070_:
{
uint8_t v___x_1075_; 
v___x_1075_ = l_Lean_Expr_hasMVar(v_a_986_);
if (v___x_1075_ == 0)
{
v___y_988_ = v___y_1071_;
v___y_989_ = v___y_1072_;
v___y_990_ = v___y_1073_;
v___y_991_ = v___y_1074_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v___x_1076_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1077_ = l_Lean_MessageData_ofName(v_tacticName_969_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_indentExpr(v_a_986_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1082_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1109_, lean_object* v_e_1110_, lean_object* v_axiomDeclRange_x3f_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1109_, v_e_1110_, v_axiomDeclRange_x3f_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_axiomDeclRange_x3f_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(lean_object* v_env_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_1118_, v___y_1120_, v___y_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(lean_object* v_env_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(v_env_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_00_u03b1_1132_, lean_object* v_env_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_1133_, v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_env_1142_, lean_object* v_x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(v_00_u03b1_1141_, v_env_1142_, v_x_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(lean_object* v_stx_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1150_, v___y_1153_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(lean_object* v_stx_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v_stx_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(lean_object* v_declName_1164_, lean_object* v_declRanges_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1164_, v_declRanges_1165_, v___y_1167_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(lean_object* v_declName_1172_, lean_object* v_declRanges_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_1172_, v_declRanges_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1179_;
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
