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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v_tacticName_408_, lean_object* v___x_409_, lean_object* v_a_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_419_; lean_object* v___x_428_; lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_603_; 
v___x_428_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_406_, v___y_414_);
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_603_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_603_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_603_;
goto v_resetjp_430_;
}
v___jp_416_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v___y_418_);
v___x_420_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_421_ = l_Lean_MessageData_ofName(v_tacticName_408_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_Exception_toMessageData(v___y_417_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_426_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v___x_427_;
}
else
{
lean_dec_ref(v___y_417_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v_tacticName_408_);
return v___y_418_;
}
}
v_resetjp_430_:
{
lean_object* v___y_434_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___x_459_; lean_object* v_options_460_; lean_object* v_env_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_459_ = lean_st_ref_get(v___y_414_);
v_options_460_ = lean_ctor_get(v___y_413_, 2);
v_env_461_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_env_461_);
lean_dec(v___x_459_);
v___x_462_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc(v_a_429_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v_a_429_);
lean_ctor_set(v___x_463_, 1, v___x_407_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
v___x_464_ = lean_box(1);
v___x_465_ = 1;
lean_inc(v_a_429_);
v___x_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_466_, 0, v_a_429_);
lean_ctor_set(v___x_466_, 1, v___x_409_);
v___x_467_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_467_, 0, v___x_463_);
lean_ctor_set(v___x_467_, 1, v_a_410_);
lean_ctor_set(v___x_467_, 2, v___x_464_);
lean_ctor_set(v___x_467_, 3, v___x_466_);
lean_ctor_set_uint8(v___x_467_, sizeof(void*)*4, v___x_465_);
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 1);
lean_ctor_set(v___x_431_, 0, v___x_467_);
v___x_469_ = v___x_431_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_602_;
goto v_reusejp_468_;
}
v___jp_433_:
{
if (lean_obj_tag(v___y_434_) == 0)
{
lean_object* v___x_435_; 
lean_dec_ref(v___y_434_);
v___x_435_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_a_429_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v_tacticName_408_);
return v___x_435_;
}
else
{
lean_object* v_a_436_; uint8_t v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
v___x_437_ = l_Lean_Exception_isInterrupt(v_a_436_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v_a_436_);
v___x_438_ = l_Lean_Exception_isRuntime(v_a_436_);
v___y_417_ = v_a_436_;
v___y_418_ = v___x_435_;
v___y_419_ = v___x_438_;
goto v___jp_416_;
}
else
{
v___y_417_ = v_a_436_;
v___y_418_ = v___x_435_;
v___y_419_ = v___x_437_;
goto v___jp_416_;
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_429_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v_tacticName_408_);
v_a_439_ = lean_ctor_get(v___y_434_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___y_434_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___y_434_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___y_434_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
v___jp_447_:
{
if (v___y_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v___y_449_);
v___x_451_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_408_);
v___x_452_ = l_Lean_MessageData_ofName(v_tacticName_408_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_Exception_toMessageData(v___y_448_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_457_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
v___y_434_ = v___x_458_;
goto v___jp_433_;
}
else
{
lean_dec_ref(v___y_448_);
v___y_434_ = v___y_449_;
goto v___jp_433_;
}
}
v_reusejp_468_:
{
uint8_t v___x_470_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v_fileName_475_; lean_object* v_fileMap_476_; lean_object* v_currRecDepth_477_; lean_object* v_ref_478_; lean_object* v_currNamespace_479_; lean_object* v_openDecls_480_; lean_object* v_initHeartbeats_481_; lean_object* v_maxHeartbeats_482_; lean_object* v_quotContext_483_; lean_object* v_currMacroScope_484_; lean_object* v_cancelTk_x3f_485_; uint8_t v_suppressElabErrors_486_; lean_object* v_inheritedTraceOptions_487_; lean_object* v___y_488_; lean_object* v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; uint8_t v___y_519_; uint8_t v___y_520_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___y_547_; lean_object* v___y_548_; uint8_t v___y_580_; uint8_t v___x_601_; 
v___x_470_ = 1;
v___x_541_ = l_Lean_Elab_async;
v___x_542_ = 0;
lean_inc_ref(v_options_460_);
v___x_543_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_options_460_, v___x_541_, v___x_542_);
v___x_544_ = l_Lean_diagnostics;
v___x_545_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_543_, v___x_544_);
v___x_601_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_461_);
lean_dec_ref(v_env_461_);
if (v___x_601_ == 0)
{
if (v___x_545_ == 0)
{
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___y_547_ = v___y_413_;
v___y_548_ = v___y_414_;
goto v___jp_546_;
}
else
{
v___y_580_ = v___x_601_;
goto v___jp_579_;
}
}
else
{
v___y_580_ = v___x_545_;
goto v___jp_579_;
}
v___jp_471_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_473_, v___y_472_);
lean_dec_ref(v___y_472_);
v___x_490_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_490_, 0, v_fileName_475_);
lean_ctor_set(v___x_490_, 1, v_fileMap_476_);
lean_ctor_set(v___x_490_, 2, v___y_473_);
lean_ctor_set(v___x_490_, 3, v_currRecDepth_477_);
lean_ctor_set(v___x_490_, 4, v___x_489_);
lean_ctor_set(v___x_490_, 5, v_ref_478_);
lean_ctor_set(v___x_490_, 6, v_currNamespace_479_);
lean_ctor_set(v___x_490_, 7, v_openDecls_480_);
lean_ctor_set(v___x_490_, 8, v_initHeartbeats_481_);
lean_ctor_set(v___x_490_, 9, v_maxHeartbeats_482_);
lean_ctor_set(v___x_490_, 10, v_quotContext_483_);
lean_ctor_set(v___x_490_, 11, v_currMacroScope_484_);
lean_ctor_set(v___x_490_, 12, v_cancelTk_x3f_485_);
lean_ctor_set(v___x_490_, 13, v_inheritedTraceOptions_487_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*14, v___y_474_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*14 + 1, v_suppressElabErrors_486_);
v___x_491_ = l_Lean_addAndCompile(v___x_469_, v___x_470_, v___x_490_, v___y_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
v___y_434_ = v___x_491_;
goto v___jp_433_;
}
else
{
lean_object* v_a_492_; uint8_t v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
v___x_493_ = l_Lean_Exception_isInterrupt(v_a_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
lean_inc(v_a_492_);
v___x_494_ = l_Lean_Exception_isRuntime(v_a_492_);
v___y_448_ = v_a_492_;
v___y_449_ = v___x_491_;
v___y_450_ = v___x_494_;
goto v___jp_447_;
}
else
{
v___y_448_ = v_a_492_;
v___y_449_ = v___x_491_;
v___y_450_ = v___x_493_;
goto v___jp_447_;
}
}
}
v___jp_495_:
{
lean_object* v_fileName_501_; lean_object* v_fileMap_502_; lean_object* v_currRecDepth_503_; lean_object* v_ref_504_; lean_object* v_currNamespace_505_; lean_object* v_openDecls_506_; lean_object* v_initHeartbeats_507_; lean_object* v_maxHeartbeats_508_; lean_object* v_quotContext_509_; lean_object* v_currMacroScope_510_; lean_object* v_cancelTk_x3f_511_; uint8_t v_suppressElabErrors_512_; lean_object* v_inheritedTraceOptions_513_; 
v_fileName_501_ = lean_ctor_get(v___y_499_, 0);
lean_inc_ref(v_fileName_501_);
v_fileMap_502_ = lean_ctor_get(v___y_499_, 1);
lean_inc_ref(v_fileMap_502_);
v_currRecDepth_503_ = lean_ctor_get(v___y_499_, 3);
lean_inc(v_currRecDepth_503_);
v_ref_504_ = lean_ctor_get(v___y_499_, 5);
lean_inc(v_ref_504_);
v_currNamespace_505_ = lean_ctor_get(v___y_499_, 6);
lean_inc(v_currNamespace_505_);
v_openDecls_506_ = lean_ctor_get(v___y_499_, 7);
lean_inc(v_openDecls_506_);
v_initHeartbeats_507_ = lean_ctor_get(v___y_499_, 8);
lean_inc(v_initHeartbeats_507_);
v_maxHeartbeats_508_ = lean_ctor_get(v___y_499_, 9);
lean_inc(v_maxHeartbeats_508_);
v_quotContext_509_ = lean_ctor_get(v___y_499_, 10);
lean_inc(v_quotContext_509_);
v_currMacroScope_510_ = lean_ctor_get(v___y_499_, 11);
lean_inc(v_currMacroScope_510_);
v_cancelTk_x3f_511_ = lean_ctor_get(v___y_499_, 12);
lean_inc(v_cancelTk_x3f_511_);
v_suppressElabErrors_512_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_513_ = lean_ctor_get(v___y_499_, 13);
lean_inc_ref(v_inheritedTraceOptions_513_);
lean_dec_ref(v___y_499_);
v___y_472_ = v___y_496_;
v___y_473_ = v___y_497_;
v___y_474_ = v___y_498_;
v_fileName_475_ = v_fileName_501_;
v_fileMap_476_ = v_fileMap_502_;
v_currRecDepth_477_ = v_currRecDepth_503_;
v_ref_478_ = v_ref_504_;
v_currNamespace_479_ = v_currNamespace_505_;
v_openDecls_480_ = v_openDecls_506_;
v_initHeartbeats_481_ = v_initHeartbeats_507_;
v_maxHeartbeats_482_ = v_maxHeartbeats_508_;
v_quotContext_483_ = v_quotContext_509_;
v_currMacroScope_484_ = v_currMacroScope_510_;
v_cancelTk_x3f_485_ = v_cancelTk_x3f_511_;
v_suppressElabErrors_486_ = v_suppressElabErrors_512_;
v_inheritedTraceOptions_487_ = v_inheritedTraceOptions_513_;
v___y_488_ = v___y_500_;
goto v___jp_471_;
}
v___jp_514_:
{
if (v___y_520_ == 0)
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_traceState_526_; lean_object* v_messages_527_; lean_object* v_infoState_528_; lean_object* v_snapshotTasks_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_539_; 
v___x_521_ = lean_st_ref_take(v___y_518_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_521_, 1);
v_ngen_524_ = lean_ctor_get(v___x_521_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_521_, 3);
v_traceState_526_ = lean_ctor_get(v___x_521_, 4);
v_messages_527_ = lean_ctor_get(v___x_521_, 6);
v_infoState_528_ = lean_ctor_get(v___x_521_, 7);
v_snapshotTasks_529_ = lean_ctor_get(v___x_521_, 8);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_521_, 5);
lean_dec(v_unused_540_);
v___x_531_ = v___x_521_;
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snapshotTasks_529_);
lean_inc(v_infoState_528_);
lean_inc(v_messages_527_);
lean_inc(v_traceState_526_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_521_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = l_Lean_Kernel_enableDiag(v_env_522_, v___y_519_);
v___x_534_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 5, v___x_534_);
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_traceState_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_538_, 6, v_messages_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 7, v_infoState_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 8, v_snapshotTasks_529_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_st_ref_set(v___y_518_, v___x_536_);
v___y_496_ = v___y_516_;
v___y_497_ = v___y_515_;
v___y_498_ = v___y_519_;
v___y_499_ = v___y_517_;
v___y_500_ = v___y_518_;
goto v___jp_495_;
}
}
}
else
{
v___y_496_ = v___y_516_;
v___y_497_ = v___y_515_;
v___y_498_ = v___y_519_;
v___y_499_ = v___y_517_;
v___y_500_ = v___y_518_;
goto v___jp_495_;
}
}
v___jp_546_:
{
lean_object* v___x_549_; lean_object* v_fileName_550_; lean_object* v_fileMap_551_; lean_object* v_currRecDepth_552_; lean_object* v_ref_553_; lean_object* v_currNamespace_554_; lean_object* v_openDecls_555_; lean_object* v_initHeartbeats_556_; lean_object* v_maxHeartbeats_557_; lean_object* v_quotContext_558_; lean_object* v_currMacroScope_559_; lean_object* v_cancelTk_x3f_560_; uint8_t v_suppressElabErrors_561_; lean_object* v_inheritedTraceOptions_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_576_; 
v___x_549_ = lean_st_ref_get(v___y_548_);
v_fileName_550_ = lean_ctor_get(v___y_547_, 0);
v_fileMap_551_ = lean_ctor_get(v___y_547_, 1);
v_currRecDepth_552_ = lean_ctor_get(v___y_547_, 3);
v_ref_553_ = lean_ctor_get(v___y_547_, 5);
v_currNamespace_554_ = lean_ctor_get(v___y_547_, 6);
v_openDecls_555_ = lean_ctor_get(v___y_547_, 7);
v_initHeartbeats_556_ = lean_ctor_get(v___y_547_, 8);
v_maxHeartbeats_557_ = lean_ctor_get(v___y_547_, 9);
v_quotContext_558_ = lean_ctor_get(v___y_547_, 10);
v_currMacroScope_559_ = lean_ctor_get(v___y_547_, 11);
v_cancelTk_x3f_560_ = lean_ctor_get(v___y_547_, 12);
v_suppressElabErrors_561_ = lean_ctor_get_uint8(v___y_547_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_562_ = lean_ctor_get(v___y_547_, 13);
v_isSharedCheck_576_ = !lean_is_exclusive(v___y_547_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; 
v_unused_577_ = lean_ctor_get(v___y_547_, 4);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v___y_547_, 2);
lean_dec(v_unused_578_);
v___x_564_ = v___y_547_;
v_isShared_565_ = v_isSharedCheck_576_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_inheritedTraceOptions_562_);
lean_inc(v_cancelTk_x3f_560_);
lean_inc(v_currMacroScope_559_);
lean_inc(v_quotContext_558_);
lean_inc(v_maxHeartbeats_557_);
lean_inc(v_initHeartbeats_556_);
lean_inc(v_openDecls_555_);
lean_inc(v_currNamespace_554_);
lean_inc(v_ref_553_);
lean_inc(v_currRecDepth_552_);
lean_inc(v_fileMap_551_);
lean_inc(v_fileName_550_);
lean_dec(v___y_547_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_576_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_env_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v_env_566_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_env_566_);
lean_dec(v___x_549_);
v___x_567_ = l_Lean_maxRecDepth;
v___x_568_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_543_, v___x_567_);
lean_inc_ref(v_inheritedTraceOptions_562_);
lean_inc(v_cancelTk_x3f_560_);
lean_inc(v_currMacroScope_559_);
lean_inc(v_quotContext_558_);
lean_inc(v_maxHeartbeats_557_);
lean_inc(v_initHeartbeats_556_);
lean_inc(v_openDecls_555_);
lean_inc(v_currNamespace_554_);
lean_inc(v_ref_553_);
lean_inc(v_currRecDepth_552_);
lean_inc_ref(v___x_543_);
lean_inc_ref(v_fileMap_551_);
lean_inc_ref(v_fileName_550_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v___x_568_);
lean_ctor_set(v___x_564_, 2, v___x_543_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_fileName_550_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_fileMap_551_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_currRecDepth_552_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v_ref_553_);
lean_ctor_set(v_reuseFailAlloc_575_, 6, v_currNamespace_554_);
lean_ctor_set(v_reuseFailAlloc_575_, 7, v_openDecls_555_);
lean_ctor_set(v_reuseFailAlloc_575_, 8, v_initHeartbeats_556_);
lean_ctor_set(v_reuseFailAlloc_575_, 9, v_maxHeartbeats_557_);
lean_ctor_set(v_reuseFailAlloc_575_, 10, v_quotContext_558_);
lean_ctor_set(v_reuseFailAlloc_575_, 11, v_currMacroScope_559_);
lean_ctor_set(v_reuseFailAlloc_575_, 12, v_cancelTk_x3f_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 13, v_inheritedTraceOptions_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_575_, sizeof(void*)*14 + 1, v_suppressElabErrors_561_);
v___x_570_ = v_reuseFailAlloc_575_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; 
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*14, v___x_545_);
v___x_571_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_572_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___x_543_, v___x_571_, v___x_542_);
v___x_573_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_572_, v___x_544_);
v___x_574_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_566_);
lean_dec_ref(v_env_566_);
if (v___x_574_ == 0)
{
if (v___x_573_ == 0)
{
lean_dec_ref(v___x_570_);
v___y_472_ = v___x_567_;
v___y_473_ = v___x_572_;
v___y_474_ = v___x_573_;
v_fileName_475_ = v_fileName_550_;
v_fileMap_476_ = v_fileMap_551_;
v_currRecDepth_477_ = v_currRecDepth_552_;
v_ref_478_ = v_ref_553_;
v_currNamespace_479_ = v_currNamespace_554_;
v_openDecls_480_ = v_openDecls_555_;
v_initHeartbeats_481_ = v_initHeartbeats_556_;
v_maxHeartbeats_482_ = v_maxHeartbeats_557_;
v_quotContext_483_ = v_quotContext_558_;
v_currMacroScope_484_ = v_currMacroScope_559_;
v_cancelTk_x3f_485_ = v_cancelTk_x3f_560_;
v_suppressElabErrors_486_ = v_suppressElabErrors_561_;
v_inheritedTraceOptions_487_ = v_inheritedTraceOptions_562_;
v___y_488_ = v___y_548_;
goto v___jp_471_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_562_);
lean_dec(v_cancelTk_x3f_560_);
lean_dec(v_currMacroScope_559_);
lean_dec(v_quotContext_558_);
lean_dec(v_maxHeartbeats_557_);
lean_dec(v_initHeartbeats_556_);
lean_dec(v_openDecls_555_);
lean_dec(v_currNamespace_554_);
lean_dec(v_ref_553_);
lean_dec(v_currRecDepth_552_);
lean_dec_ref(v_fileMap_551_);
lean_dec_ref(v_fileName_550_);
v___y_515_ = v___x_572_;
v___y_516_ = v___x_567_;
v___y_517_ = v___x_570_;
v___y_518_ = v___y_548_;
v___y_519_ = v___x_573_;
v___y_520_ = v___x_574_;
goto v___jp_514_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_562_);
lean_dec(v_cancelTk_x3f_560_);
lean_dec(v_currMacroScope_559_);
lean_dec(v_quotContext_558_);
lean_dec(v_maxHeartbeats_557_);
lean_dec(v_initHeartbeats_556_);
lean_dec(v_openDecls_555_);
lean_dec(v_currNamespace_554_);
lean_dec(v_ref_553_);
lean_dec(v_currRecDepth_552_);
lean_dec_ref(v_fileMap_551_);
lean_dec_ref(v_fileName_550_);
v___y_515_ = v___x_572_;
v___y_516_ = v___x_567_;
v___y_517_ = v___x_570_;
v___y_518_ = v___y_548_;
v___y_519_ = v___x_573_;
v___y_520_ = v___x_573_;
goto v___jp_514_;
}
}
}
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v_nextMacroScope_583_; lean_object* v_ngen_584_; lean_object* v_auxDeclNGen_585_; lean_object* v_traceState_586_; lean_object* v_messages_587_; lean_object* v_infoState_588_; lean_object* v_snapshotTasks_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_599_; 
v___x_581_ = lean_st_ref_take(v___y_414_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
v_nextMacroScope_583_ = lean_ctor_get(v___x_581_, 1);
v_ngen_584_ = lean_ctor_get(v___x_581_, 2);
v_auxDeclNGen_585_ = lean_ctor_get(v___x_581_, 3);
v_traceState_586_ = lean_ctor_get(v___x_581_, 4);
v_messages_587_ = lean_ctor_get(v___x_581_, 6);
v_infoState_588_ = lean_ctor_get(v___x_581_, 7);
v_snapshotTasks_589_ = lean_ctor_get(v___x_581_, 8);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_581_, 5);
lean_dec(v_unused_600_);
v___x_591_ = v___x_581_;
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snapshotTasks_589_);
lean_inc(v_infoState_588_);
lean_inc(v_messages_587_);
lean_inc(v_traceState_586_);
lean_inc(v_auxDeclNGen_585_);
lean_inc(v_ngen_584_);
lean_inc(v_nextMacroScope_583_);
lean_inc(v_env_582_);
lean_dec(v___x_581_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_593_ = l_Lean_Kernel_enableDiag(v_env_582_, v___x_545_);
v___x_594_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 5, v___x_594_);
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_nextMacroScope_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_ngen_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_auxDeclNGen_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_traceState_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_messages_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_infoState_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_snapshotTasks_589_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_st_ref_set(v___y_414_, v___x_596_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___y_547_ = v___y_413_;
v___y_548_ = v___y_414_;
goto v___jp_546_;
}
}
}
else
{
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___y_547_ = v___y_413_;
v___y_548_ = v___y_414_;
goto v___jp_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v_tacticName_606_, lean_object* v___x_607_, lean_object* v_a_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_604_, v___x_605_, v_tacticName_606_, v___x_607_, v_a_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object* v_stx_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_618_; lean_object* v___x_619_; 
v___x_618_ = 0;
v___x_619_ = l_Lean_Syntax_getRange_x3f(v_stx_615_, v___x_618_);
if (lean_obj_tag(v___x_619_) == 1)
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_632_; 
v_val_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_632_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fileMap_624_; lean_object* v_start_625_; lean_object* v_stop_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v_fileMap_624_ = lean_ctor_get(v___y_616_, 1);
lean_inc_ref(v_fileMap_624_);
lean_dec_ref(v___y_616_);
v_start_625_ = lean_ctor_get(v_val_620_, 0);
lean_inc(v_start_625_);
v_stop_626_ = lean_ctor_get(v_val_620_, 1);
lean_inc(v_stop_626_);
lean_dec(v_val_620_);
v___x_627_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_624_, v_start_625_, v_stop_626_);
lean_dec(v_stop_626_);
lean_dec(v_start_625_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_627_);
v___x_629_ = v___x_622_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_631_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___x_619_);
lean_dec_ref(v___y_616_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object* v_stx_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_635_, v___y_636_);
lean_dec(v_stx_635_);
return v_res_638_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_640_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_ctor_set(v___x_640_, 2, v___x_639_);
lean_ctor_set(v___x_640_, 3, v___x_639_);
lean_ctor_set(v___x_640_, 4, v___x_639_);
lean_ctor_set(v___x_640_, 5, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(lean_object* v_declName_641_, lean_object* v_declRanges_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_Name_isAnonymous(v_declName_641_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v_nextMacroScope_649_; lean_object* v_ngen_650_; lean_object* v_auxDeclNGen_651_; lean_object* v_traceState_652_; lean_object* v_messages_653_; lean_object* v_infoState_654_; lean_object* v_snapshotTasks_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_683_; 
v___x_647_ = lean_st_ref_take(v___y_644_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
v_nextMacroScope_649_ = lean_ctor_get(v___x_647_, 1);
v_ngen_650_ = lean_ctor_get(v___x_647_, 2);
v_auxDeclNGen_651_ = lean_ctor_get(v___x_647_, 3);
v_traceState_652_ = lean_ctor_get(v___x_647_, 4);
v_messages_653_ = lean_ctor_get(v___x_647_, 6);
v_infoState_654_ = lean_ctor_get(v___x_647_, 7);
v_snapshotTasks_655_ = lean_ctor_get(v___x_647_, 8);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_647_, 5);
lean_dec(v_unused_684_);
v___x_657_ = v___x_647_;
v_isShared_658_ = v_isSharedCheck_683_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snapshotTasks_655_);
lean_inc(v_infoState_654_);
lean_inc(v_messages_653_);
lean_inc(v_traceState_652_);
lean_inc(v_auxDeclNGen_651_);
lean_inc(v_ngen_650_);
lean_inc(v_nextMacroScope_649_);
lean_inc(v_env_648_);
lean_dec(v___x_647_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_683_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_659_ = l_Lean_declRangeExt;
v___x_660_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_659_, v_env_648_, v_declName_641_, v_declRanges_642_);
v___x_661_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 5, v___x_661_);
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_nextMacroScope_649_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_ngen_650_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_auxDeclNGen_651_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_traceState_652_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_messages_653_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_infoState_654_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_snapshotTasks_655_);
v___x_663_ = v_reuseFailAlloc_682_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_mctx_666_; lean_object* v_zetaDeltaFVarIds_667_; lean_object* v_postponed_668_; lean_object* v_diag_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_680_; 
v___x_664_ = lean_st_ref_set(v___y_644_, v___x_663_);
v___x_665_ = lean_st_ref_take(v___y_643_);
v_mctx_666_ = lean_ctor_get(v___x_665_, 0);
v_zetaDeltaFVarIds_667_ = lean_ctor_get(v___x_665_, 2);
v_postponed_668_ = lean_ctor_get(v___x_665_, 3);
v_diag_669_ = lean_ctor_get(v___x_665_, 4);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_665_, 1);
lean_dec(v_unused_681_);
v___x_671_ = v___x_665_;
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_diag_669_);
lean_inc(v_postponed_668_);
lean_inc(v_zetaDeltaFVarIds_667_);
lean_inc(v_mctx_666_);
lean_dec(v___x_665_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_mctx_666_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_zetaDeltaFVarIds_667_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_postponed_668_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_diag_669_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_st_ref_set(v___y_643_, v___x_675_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v_declRanges_642_);
lean_dec(v_declName_641_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(lean_object* v_declName_687_, lean_object* v_declRanges_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_687_, v_declRanges_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec(v___y_689_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_declName_693_, lean_object* v_rangeStx_694_, lean_object* v_selectionRangeStx_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_718_; 
lean_inc_ref(v___y_698_);
v___x_701_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_694_, v___y_698_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_718_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_718_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_718_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
if (lean_obj_tag(v_a_702_) == 1)
{
lean_object* v_val_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v_a_710_; 
lean_del_object(v___x_704_);
v_val_706_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_val_706_);
lean_dec_ref(v_a_702_);
v___x_707_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_695_, v___y_698_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
if (lean_obj_tag(v_a_708_) == 0)
{
lean_inc(v_val_706_);
v_a_710_ = v_val_706_;
goto v___jp_709_;
}
else
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v_a_708_);
v_a_710_ = v_val_713_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_val_706_);
lean_ctor_set(v___x_711_, 1, v_a_710_);
v___x_712_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_693_, v___x_711_, v___y_697_, v___y_699_);
return v___x_712_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_a_702_);
lean_dec_ref(v___y_698_);
lean_dec(v_declName_693_);
v___x_714_ = lean_box(0);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_714_);
v___x_716_ = v___x_704_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_declName_719_, lean_object* v_rangeStx_720_, lean_object* v_selectionRangeStx_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_declName_719_, v_rangeStx_720_, v_selectionRangeStx_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v_selectionRangeStx_721_);
lean_dec(v_rangeStx_720_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_object* v___x_730_; 
v___x_730_ = l_List_reverse___redArg(v_a_729_);
return v___x_730_;
}
else
{
lean_object* v_head_731_; lean_object* v_tail_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_741_; 
v_head_731_ = lean_ctor_get(v_a_728_, 0);
v_tail_732_ = lean_ctor_get(v_a_728_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_734_ = v_a_728_;
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_tail_732_);
lean_inc(v_head_731_);
lean_dec(v_a_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = l_Lean_mkLevelParam(v_head_731_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_729_);
lean_ctor_set(v___x_734_, 0, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_a_729_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
v_a_728_ = v_tail_732_;
v_a_729_ = v___x_738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(lean_object* v_env_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; lean_object* v_nextMacroScope_747_; lean_object* v_ngen_748_; lean_object* v_auxDeclNGen_749_; lean_object* v_traceState_750_; lean_object* v_messages_751_; lean_object* v_infoState_752_; lean_object* v_snapshotTasks_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_779_; 
v___x_746_ = lean_st_ref_take(v___y_744_);
v_nextMacroScope_747_ = lean_ctor_get(v___x_746_, 1);
v_ngen_748_ = lean_ctor_get(v___x_746_, 2);
v_auxDeclNGen_749_ = lean_ctor_get(v___x_746_, 3);
v_traceState_750_ = lean_ctor_get(v___x_746_, 4);
v_messages_751_ = lean_ctor_get(v___x_746_, 6);
v_infoState_752_ = lean_ctor_get(v___x_746_, 7);
v_snapshotTasks_753_ = lean_ctor_get(v___x_746_, 8);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; 
v_unused_780_ = lean_ctor_get(v___x_746_, 5);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_781_);
v___x_755_ = v___x_746_;
v_isShared_756_ = v_isSharedCheck_779_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snapshotTasks_753_);
lean_inc(v_infoState_752_);
lean_inc(v_messages_751_);
lean_inc(v_traceState_750_);
lean_inc(v_auxDeclNGen_749_);
lean_inc(v_ngen_748_);
lean_inc(v_nextMacroScope_747_);
lean_dec(v___x_746_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_779_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 5, v___x_757_);
lean_ctor_set(v___x_755_, 0, v_env_742_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_env_742_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_nextMacroScope_747_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_ngen_748_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_auxDeclNGen_749_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_traceState_750_);
lean_ctor_set(v_reuseFailAlloc_778_, 5, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_778_, 6, v_messages_751_);
lean_ctor_set(v_reuseFailAlloc_778_, 7, v_infoState_752_);
lean_ctor_set(v_reuseFailAlloc_778_, 8, v_snapshotTasks_753_);
v___x_759_ = v_reuseFailAlloc_778_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_mctx_762_; lean_object* v_zetaDeltaFVarIds_763_; lean_object* v_postponed_764_; lean_object* v_diag_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_776_; 
v___x_760_ = lean_st_ref_set(v___y_744_, v___x_759_);
v___x_761_ = lean_st_ref_take(v___y_743_);
v_mctx_762_ = lean_ctor_get(v___x_761_, 0);
v_zetaDeltaFVarIds_763_ = lean_ctor_get(v___x_761_, 2);
v_postponed_764_ = lean_ctor_get(v___x_761_, 3);
v_diag_765_ = lean_ctor_get(v___x_761_, 4);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___x_761_, 1);
lean_dec(v_unused_777_);
v___x_767_ = v___x_761_;
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_diag_765_);
lean_inc(v_postponed_764_);
lean_inc(v_zetaDeltaFVarIds_763_);
lean_inc(v_mctx_762_);
lean_dec(v___x_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___closed__0);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_mctx_762_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_zetaDeltaFVarIds_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_postponed_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_diag_765_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_st_ref_set(v___y_743_, v___x_771_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(lean_object* v_env_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(lean_object* v_env_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v_env_795_; lean_object* v_a_797_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_794_ = lean_st_ref_get(v___y_792_);
v_env_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_env_795_);
lean_dec(v___x_794_);
v___x_807_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_787_, v___y_790_, v___y_792_);
lean_dec_ref(v___x_807_);
lean_inc(v___y_792_);
lean_inc(v___y_790_);
v___x_808_ = lean_apply_5(v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, lean_box(0));
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___x_810_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_795_, v___y_790_, v___y_792_);
lean_dec(v___y_792_);
lean_dec(v___y_790_);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_810_, 0);
lean_dec(v_unused_818_);
v___x_812_ = v___x_810_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_dec(v___x_810_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_a_809_);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_809_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_819_; 
v_a_819_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v___x_808_);
v_a_797_ = v_a_819_;
goto v___jp_796_;
}
v___jp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v___x_798_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_795_, v___y_790_, v___y_792_);
lean_dec(v___y_792_);
lean_dec(v___y_790_);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_798_, 0);
lean_dec(v_unused_806_);
v___x_800_ = v___x_798_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_dec(v___x_798_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 0, v_a_797_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_797_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(lean_object* v_env_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v_res_827_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_unsigned_to_nat(16u);
v___x_830_ = lean_mk_array(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_837_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = l_Lean_Level_ofNat(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_box(0);
v___x_854_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_857_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_box(0);
v___x_860_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_861_ = l_Lean_mkConst(v___x_860_, v___x_859_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_box(0);
v___x_867_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_868_ = l_Lean_mkConst(v___x_867_, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_875_, lean_object* v_e_876_, lean_object* v_axiomDeclRange_x3f_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; uint8_t v___x_998_; 
v___x_891_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_876_, v_a_879_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
v___x_998_ = l_Lean_Expr_hasFVar(v_a_892_);
if (v___x_998_ == 0)
{
v___y_977_ = v_a_878_;
v___y_978_ = v_a_879_;
v___y_979_ = v_a_880_;
v___y_980_ = v_a_881_;
goto v___jp_976_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v___x_999_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1000_ = l_Lean_MessageData_ofName(v_tacticName_875_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_indentExpr(v_a_892_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1005_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
v___jp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_886_ = lean_box(0);
v___x_887_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_885_, v___x_886_);
v___x_888_ = l_Lean_mkConst(v___y_884_, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
v___jp_893_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_params_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_973_; 
v___x_898_ = lean_st_ref_get(v___y_897_);
v___x_899_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_892_);
v___x_900_ = l_Lean_collectLevelParams(v___x_899_, v_a_892_);
v_params_901_ = lean_ctor_get(v___x_900_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_974_ = lean_ctor_get(v___x_900_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_975_);
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_973_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_params_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_973_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_env_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_env_905_ = lean_ctor_get(v___x_898_, 0);
lean_inc_ref(v_env_905_);
lean_dec(v___x_898_);
v___x_906_ = lean_box(0);
v___x_907_ = lean_array_to_list(v_params_901_);
v___x_908_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_875_);
v___x_909_ = l_Lean_Name_append(v___x_908_, v_tacticName_875_);
v___x_910_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_909_);
v___x_911_ = l_Lean_Name_append(v___x_909_, v___x_910_);
lean_inc(v_a_892_);
lean_inc(v___x_907_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_912_, 0, v___x_911_);
lean_closure_set(v___f_912_, 1, v___x_907_);
lean_closure_set(v___f_912_, 2, v_tacticName_875_);
lean_closure_set(v___f_912_, 3, v___x_906_);
lean_closure_set(v___f_912_, 4, v_a_892_);
v___x_913_ = l_Lean_Environment_unlockAsync(v_env_905_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
v___x_914_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v___x_913_, v___f_912_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_964_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_964_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_964_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_964_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___x_919_; 
v___x_919_ = lean_unbox(v_a_915_);
lean_dec(v_a_915_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v___x_909_);
lean_dec(v___x_907_);
lean_del_object(v___x_903_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v_a_892_);
v___x_920_ = lean_box(1);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_917_);
v___x_924_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_925_ = l_Lean_Name_append(v___x_909_, v___x_924_);
v___x_926_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_925_, v___y_897_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_963_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_963_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_963_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_931_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_932_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_933_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_934_ = l_Lean_mkApp3(v___x_931_, v___x_932_, v_a_892_, v___x_933_);
lean_inc(v___x_907_);
lean_inc(v_a_927_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_934_);
lean_ctor_set(v___x_903_, 1, v___x_907_);
lean_ctor_set(v___x_903_, 0, v_a_927_);
v___x_936_ = v___x_903_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_927_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v___x_934_);
v___x_936_ = v_reuseFailAlloc_962_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = 0;
v___x_938_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*1, v___x_937_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_938_);
v___x_940_ = v___x_929_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_961_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; 
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
v___x_941_ = l_Lean_addDecl(v___x_940_, v___x_937_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_dec_ref(v___x_941_);
if (lean_obj_tag(v_axiomDeclRange_x3f_877_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_val_942_ = lean_ctor_get(v_axiomDeclRange_x3f_877_, 0);
v___x_943_ = lean_box(0);
lean_inc(v_a_927_);
v___x_944_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_927_, v_val_942_, v___x_943_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref(v___x_944_);
v___y_884_ = v_a_927_;
v___y_885_ = v___x_907_;
goto v___jp_883_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_927_);
lean_dec(v___x_907_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
v___y_884_ = v_a_927_;
v___y_885_ = v___x_907_;
goto v___jp_883_;
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_a_927_);
lean_dec(v___x_907_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
v_a_953_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_941_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_941_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
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
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec(v___x_909_);
lean_dec(v___x_907_);
lean_del_object(v___x_903_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v_a_892_);
v_a_965_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_914_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_914_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
v___jp_976_:
{
uint8_t v___x_981_; 
v___x_981_ = l_Lean_Expr_hasMVar(v_a_892_);
if (v___x_981_ == 0)
{
v___y_894_ = v___y_977_;
v___y_895_ = v___y_978_;
v___y_896_ = v___y_979_;
v___y_897_ = v___y_980_;
goto v___jp_893_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v___x_982_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_983_ = l_Lean_MessageData_ofName(v_tacticName_875_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_indentExpr(v_a_892_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_988_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1015_, lean_object* v_e_1016_, lean_object* v_axiomDeclRange_x3f_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1015_, v_e_1016_, v_axiomDeclRange_x3f_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_axiomDeclRange_x3f_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(lean_object* v_env_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_1024_, v___y_1026_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(lean_object* v_env_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(v_env_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_00_u03b1_1038_, lean_object* v_env_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_1039_, v_x_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_env_1048_, lean_object* v_x_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(v_00_u03b1_1047_, v_env_1048_, v_x_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(lean_object* v_stx_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1056_, v___y_1059_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(lean_object* v_stx_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v_stx_1063_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(lean_object* v_declName_1070_, lean_object* v_declRanges_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1070_, v_declRanges_1071_, v___y_1073_, v___y_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(lean_object* v_declName_1078_, lean_object* v_declRanges_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_1078_, v_declRanges_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1085_;
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
