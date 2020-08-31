// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: Init Lean.Expr Lean.Environment Lean.Attributes Lean.ProjFns Lean.Meta.Basic
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getD___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr(lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___lambda__1(lean_object*);
lean_object* lean_get_extern_const_arity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_mkProjectionFnInfoExtension___closed__3;
extern lean_object* l_Lean_registerInternalExceptionId___closed__2;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_ExternAttrData_inhabited___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_intersperse___main___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___closed__1;
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2;
extern lean_object* l_Lean_Compiler_mkInlineAttrs___closed__3;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__3;
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__3;
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
uint8_t l_Not_Decidable___rarg(uint8_t);
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExternEntry_backend(lean_object*);
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10;
lean_object* l_Lean_ExternAttrData_inhabited;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* lean_add_extern(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_mkExternAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3;
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3;
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_object* l_Lean_mkExternAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getParamNamesImpl___closed__1;
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_3__parseOptNum___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___closed__2;
lean_object* l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_mkExternAttr___closed__1;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__1;
lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_mkExternAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__2;
lean_object* l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_registerClassAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__4;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_String_Iterator_hasNext(lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_getExternAttrData___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(lean_object*);
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
extern lean_object* l_Lean_Syntax_inhabited;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Std_RBNode_find___main___at_Lean_getExternAttrData___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___closed__3;
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___closed__5;
lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9;
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerParametricAttribute___spec__9___rarg___closed__1;
lean_object* l_Lean_mkExternAttr___closed__4;
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8;
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___boxed(lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_3__parseOptNum(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryForAux___main___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_remainingBytes(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1;
lean_object* l_Lean_getExternEntryForAux___main(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
extern lean_object* l_Lean_Environment_addAttribute___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___lambda__1___boxed(lean_object*);
lean_object* l_Lean_externAttr;
lean_object* l_Lean_mkExternAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_getExternConstArity(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_ExternAttrData_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ExternAttrData_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExternAttrData_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("string literal expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("adhoc");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("string or identifier expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Syntax_inhabited;
x_7 = lean_array_get(x_6, x_1, x_2);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = lean_nat_dec_eq(x_10, x_4);
lean_dec(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_get(x_6, x_1, x_10);
x_13 = l_Lean_Syntax_isIdOrAtom_x3f(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_isStrLit_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_15 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5;
x_23 = lean_string_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Compiler_mkInlineAttrs___closed__3;
x_25 = lean_string_dec_eq(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Syntax_isStrLit_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_27 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_2 = x_29;
x_3 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
x_33 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
x_34 = lean_array_get(x_6, x_1, x_33);
x_35 = l_Lean_Syntax_isStrLit_x3f(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_3);
x_36 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_add(x_33, x_9);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
x_2 = x_38;
x_3 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_21);
lean_dec(x_12);
x_42 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
x_2 = x_42;
x_3 = x_44;
goto _start;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_46 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7;
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2;
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_4);
lean_dec(x_2);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_3);
return x_48;
}
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("all");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid extern attribute");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of argument");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Syntax_inhabited;
x_37 = lean_array_get(x_36, x_3, x_5);
x_38 = l_Lean_numLitKind;
x_39 = l_Lean_Syntax_isNatLitAux(x_38, x_37);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_5);
x_7 = x_40;
goto block_35;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_7 = x_42;
goto block_35;
}
block_35:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_inhabited;
x_11 = lean_array_get(x_10, x_3, x_9);
x_12 = l_Lean_Syntax_isStrLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(x_3, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
x_27 = lean_nat_dec_eq(x_4, x_26);
lean_dec(x_26);
lean_dec(x_4);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_8);
x_28 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8;
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_4);
x_43 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10;
return x_43;
}
}
default: 
{
lean_object* x_44; 
x_44 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10;
return x_44;
}
}
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_addExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_extern(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ofExcept___at_Lean_mkExternAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__6___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_inhabited;
x_2 = l_Lean_ExternAttrData_inhabited;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_swap(x_3, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1;
x_10 = lean_array_get(x_9, x_3, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_Lean_Name_quickLt(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_3, x_4, x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_20 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_3 = x_17;
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_42 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1;
x_43 = lean_array_get(x_42, x_1, x_16);
x_44 = lean_array_get(x_42, x_1, x_2);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Name_quickLt(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
x_17 = x_1;
goto block_41;
}
else
{
lean_object* x_48; 
x_48 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_48;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Name_quickLt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get(x_18, x_17, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_quickLt(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(x_3, x_19, x_17, x_2, x_2);
lean_dec(x_19);
x_4 = x_27;
goto block_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
x_28 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_29 = lean_array_get(x_18, x_28, x_3);
lean_inc_n(x_2, 2);
x_30 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(x_3, x_29, x_28, x_2, x_2);
lean_dec(x_29);
x_4 = x_30;
goto block_12;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_19);
x_31 = lean_array_swap(x_17, x_2, x_3);
x_32 = lean_array_get(x_18, x_31, x_16);
x_33 = lean_array_get(x_18, x_31, x_3);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = l_Lean_Name_quickLt(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_37 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(x_3, x_33, x_31, x_2, x_2);
lean_dec(x_33);
x_4 = x_37;
goto block_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_38 = lean_array_swap(x_31, x_16, x_3);
lean_dec(x_16);
x_39 = lean_array_get(x_18, x_38, x_3);
lean_inc_n(x_2, 2);
x_40 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(x_3, x_39, x_38, x_2, x_2);
lean_dec(x_39);
x_4 = x_40;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_st_ref_get(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerParametricAttribute___spec__9___rarg___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_st_ref_take(x_13, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_st_ref_set(x_13, x_24, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
return x_3;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__8(x_18, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
x_23 = lean_st_ref_take(x_3, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_22);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_System_FilePath_dirName___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_37);
x_40 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_registerInternalExceptionId___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_44);
return x_4;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7(x_1, x_45, x_45, x_47, x_48);
lean_dec(x_47);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 5);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_57 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_57, 0, x_51);
lean_closure_set(x_57, 1, x_56);
x_58 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__8(x_57, x_46);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_53);
lean_ctor_set(x_61, 4, x_54);
lean_ctor_set(x_61, 5, x_55);
x_62 = lean_st_ref_take(x_3, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_61);
x_65 = x_61;
x_66 = lean_array_push(x_63, x_65);
x_67 = lean_st_ref_set(x_3, x_66, x_64);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
lean_dec(x_1);
x_76 = l_System_FilePath_dirName___closed__1;
x_77 = l_Lean_Name_toStringWithSep___main(x_76, x_75);
x_78 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_registerInternalExceptionId___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_46);
return x_83;
}
}
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3(x_2, x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
lean_object* _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_registerParametricAttribute___rarg___closed__1;
x_8 = l_Lean_registerParametricAttribute___rarg___closed__2;
x_9 = l_Lean_mkProjectionFnInfoExtension___closed__3;
x_10 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___closed__1;
x_11 = l_Lean_registerParametricAttribute___rarg___closed__4;
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__6(x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___rarg___lambda__5___boxed), 10, 4);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_1);
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_5);
lean_inc(x_17);
x_18 = l_Lean_registerBuiltinAttribute(x_17, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_mkExternAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(x_2);
x_7 = l_Lean_ofExcept___at_Lean_mkExternAttr___spec__1(x_6, x_3, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_mkExternAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Environment_isProjectionFn(x_10, x_1);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_1);
lean_inc(x_10);
x_12 = l_Lean_Environment_isConstructor(x_10, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_14 = lean_add_extern(x_10, x_1);
x_15 = l_Lean_ofExcept___at_Lean_registerClassAttr___spec__1(x_14, x_3, x_4, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_16, x_3, x_4, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_6);
x_23 = lean_add_extern(x_10, x_1);
x_24 = l_Lean_ofExcept___at_Lean_registerClassAttr___spec__1(x_23, x_3, x_4, x_9);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_25, x_3, x_4, x_26);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = l_Lean_Environment_isProjectionFn(x_34, x_1);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_1);
lean_inc(x_34);
x_36 = l_Lean_Environment_isConstructor(x_34, x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_add_extern(x_34, x_1);
x_40 = l_Lean_ofExcept___at_Lean_registerClassAttr___spec__1(x_39, x_3, x_4, x_33);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_41, x_3, x_4, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_add_extern(x_34, x_1);
x_49 = l_Lean_ofExcept___at_Lean_registerClassAttr___spec__1(x_48, x_3, x_4, x_33);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__5(x_50, x_3, x_4, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extern");
return x_1;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkExternAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtin and foreign functions");
return x_1;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkExternAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkExternAttr___lambda__2___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_mkExternAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_mkExternAttr___closed__2;
x_3 = l_Lean_mkExternAttr___closed__3;
x_4 = l_Lean_mkExternAttr___closed__4;
x_5 = l_Lean_mkExternAttr___closed__5;
x_6 = 0;
x_7 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* l_Lean_ofExcept___at_Lean_mkExternAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_mkExternAttr___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___main___at_Lean_mkExternAttr___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_mkExternAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkExternAttr___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_mkExternAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkExternAttr___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_RBNode_find___main___at_Lean_getExternAttrData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2);
x_7 = l_Std_RBNode_find___main___at_Lean_getExternAttrData___spec__2(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_2, x_8);
lean_dec(x_8);
x_11 = l_Lean_ExternAttrData_inhabited___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(x_10, x_12, x_16, x_15);
lean_dec(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
lean_object* lean_get_extern_attr_data(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_RBNode_find___main___at_Lean_getExternAttrData___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___main___at_Lean_getExternAttrData___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_3__parseOptNum___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = l_String_Iterator_hasNext(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = l_String_Iterator_curr(x_2);
x_11 = 48;
x_12 = x_11 <= x_10;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 57;
x_15 = x_10 <= x_14;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = l_String_Iterator_next(x_2);
x_18 = lean_unsigned_to_nat(10u);
x_19 = lean_nat_mul(x_3, x_18);
lean_dec(x_3);
x_20 = lean_uint32_to_nat(x_10);
x_21 = lean_unsigned_to_nat(48u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_add(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
x_1 = x_7;
x_2 = x_17;
x_3 = x_23;
goto _start;
}
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_3__parseOptNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_ExternAttr_3__parseOptNum___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_expandExternPatternAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = l_String_Iterator_hasNext(x_3);
if (x_9 == 0)
{
uint8_t x_29; 
x_29 = 0;
x_10 = x_29;
goto block_28;
}
else
{
uint8_t x_30; 
x_30 = 1;
x_10 = x_30;
goto block_28;
}
block_28:
{
uint8_t x_11; 
x_11 = l_Not_Decidable___rarg(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_12 = l_String_Iterator_curr(x_3);
x_13 = 35;
x_14 = x_12 == x_13;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_String_Iterator_next(x_3);
x_16 = lean_string_push(x_4, x_12);
x_2 = x_8;
x_3 = x_15;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = l_String_Iterator_next(x_3);
x_19 = l_String_Iterator_remainingBytes(x_18);
x_20 = l___private_Lean_Compiler_ExternAttr_3__parseOptNum___main(x_19, x_18, x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_sub(x_22, x_7);
lean_dec(x_22);
x_24 = l_String_splitAux___main___closed__1;
x_25 = l_List_getD___rarg(x_23, x_1, x_24);
x_26 = lean_string_append(x_4, x_25);
lean_dec(x_25);
x_2 = x_8;
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l_Lean_expandExternPatternAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_expandExternPatternAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_expandExternPattern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_string_length(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_Lean_expandExternPatternAux___main(x_2, x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_expandExternPattern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_expandExternPattern(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_mkSimpleFnCall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Prod_HasRepr___rarg___closed__1;
x_4 = lean_string_append(x_1, x_3);
x_5 = l_List_reprAux___main___rarg___closed__1;
x_6 = l_List_intersperse___main___rarg(x_5, x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_7, x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = l_Option_HasRepr___rarg___closed__3;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ExternEntry_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExternEntry_backend(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_getExternEntryForAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_ExternEntry_backend(x_4);
x_7 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_9 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_inc(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
}
}
lean_object* l_Lean_getExternEntryForAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_getExternEntryForAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_getExternEntryFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_getExternEntryForAux___main(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getExternEntryFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_isExtern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
lean_object* l_Lean_isExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExtern(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isExternC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
x_16 = 0;
return x_16;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
x_18 = 0;
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_19 = 0;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_7);
x_20 = 0;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_7);
x_21 = 0;
return x_21;
}
}
}
}
}
lean_object* l_Lean_isExternC___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExternC(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_getExternNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_externAttr;
x_5 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_4, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_getExternEntryFor(x_7, x_2);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
case 3:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
default: 
{
lean_object* x_14; 
lean_free_object(x_8);
lean_dec(x_11);
x_14 = lean_box(0);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
switch (lean_obj_tag(x_15)) {
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_box(0);
return x_20;
}
}
}
}
}
}
}
lean_object* l_Lean_getExternNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExternNameFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_environment_find(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_5);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__6___rarg(x_15, x_2, x_3, x_8);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = lean_environment_find(x_20, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__6___rarg(x_26, x_2, x_3, x_19);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_4);
lean_inc(x_5);
x_14 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_18 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_17, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_4 = x_22;
x_9 = x_20;
goto _start;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_28 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_5, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_13);
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(x_1, x_2, x_3, x_27, x_36, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_restoreSynthInstanceCache(x_29, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = l_Lean_Meta_restoreSynthInstanceCache(x_29, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_17, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_13);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_4, x_56);
lean_dec(x_4);
x_4 = x_57;
x_9 = x_55;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_4, x_61);
lean_dec(x_4);
x_63 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_5, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 2);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_13);
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_72 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(x_1, x_2, x_3, x_62, x_71, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_restoreSynthInstanceCache(x_64, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = l_Lean_Meta_restoreSynthInstanceCache(x_64, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set_tag(x_82, 1);
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_53);
if (x_87 == 0)
{
return x_53;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_53, 0);
x_89 = lean_ctor_get(x_53, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_53);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_18);
if (x_91 == 0)
{
return x_18;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_18, 0);
x_93 = lean_ctor_get(x_18, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_18);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_14, 0);
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_14);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isForall(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3(x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_expr_instantiate_rev_range(x_7, x_6, x_8, x_5);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_box(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___lambda__1___boxed), 12, 6);
lean_closure_set(x_19, 0, x_8);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
x_20 = lean_array_get_size(x_9);
x_21 = lean_nat_dec_lt(x_10, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_17, x_19, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_17);
x_23 = lean_array_fget(x_9, x_10);
lean_inc(x_11);
x_24 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_23, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_LocalDecl_type(x_25);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_27, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_23);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_10, x_31);
lean_dec(x_10);
x_10 = x_32;
x_15 = x_30;
goto _start;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_10, x_36);
lean_dec(x_10);
x_38 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 2);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_23);
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_47 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37, x_46, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_11, x_12, x_13, x_14, x_49);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = l_Lean_Meta_restoreSynthInstanceCache(x_39, x_11, x_12, x_13, x_14, x_56);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_27, x_11, x_12, x_13, x_14, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_23);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_10, x_66);
lean_dec(x_10);
x_10 = x_67;
x_15 = x_65;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_10, x_71);
lean_dec(x_10);
x_73 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_69);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_11, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_23);
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_80);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_82 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72, x_81, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_restoreSynthInstanceCache(x_74, x_11, x_12, x_13, x_14, x_84);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = l_Lean_Meta_restoreSynthInstanceCache(x_74, x_11, x_12, x_13, x_14, x_91);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set_tag(x_92, 1);
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_63);
if (x_97 == 0)
{
return x_63;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_63, 0);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_63);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_28);
if (x_101 == 0)
{
return x_28;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_28, 0);
x_103 = lean_ctor_get(x_28, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_28);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_24);
if (x_105 == 0)
{
return x_24;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_24, 0);
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_24);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_4);
lean_inc(x_5);
x_14 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__5(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_18 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main(x_17, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_4 = x_22;
x_9 = x_20;
goto _start;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_28 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_5, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_13);
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(x_1, x_2, x_3, x_27, x_36, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_restoreSynthInstanceCache(x_29, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = l_Lean_Meta_restoreSynthInstanceCache(x_29, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main(x_17, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_13);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_4, x_56);
lean_dec(x_4);
x_4 = x_57;
x_9 = x_55;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_4, x_61);
lean_dec(x_4);
x_63 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_5, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 2);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_13);
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_72 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(x_1, x_2, x_3, x_62, x_71, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_restoreSynthInstanceCache(x_64, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = l_Lean_Meta_restoreSynthInstanceCache(x_64, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set_tag(x_82, 1);
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_53);
if (x_87 == 0)
{
return x_53;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_53, 0);
x_89 = lean_ctor_get(x_53, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_53);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_18);
if (x_91 == 0)
{
return x_18;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_18, 0);
x_93 = lean_ctor_get(x_18, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_18);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_14, 0);
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_14);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_7) == 7)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_29 = lean_array_get_size(x_5);
x_30 = lean_expr_instantiate_rev_range(x_26, x_6, x_29, x_5);
lean_dec(x_29);
lean_dec(x_26);
x_31 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = (uint8_t)((x_28 << 24) >> 61);
lean_inc(x_32);
x_35 = lean_local_ctx_mk_local_decl(x_4, x_32, x_25, x_30, x_34);
x_36 = l_Lean_mkFVar(x_32);
x_37 = lean_array_push(x_5, x_36);
x_4 = x_35;
x_5 = x_37;
x_7 = x_27;
x_12 = x_33;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_5);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_8, 1);
lean_dec(x_47);
lean_ctor_set(x_8, 1, x_4);
x_48 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(x_1, x_44, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_51, 2, x_50);
x_52 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(x_1, x_44, x_5, x_6, x_51, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_expr_instantiate_rev_range(x_40, x_6, x_44, x_5);
lean_dec(x_44);
lean_dec(x_40);
x_54 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_11, x_12);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = (uint8_t)((x_42 << 24) >> 61);
lean_inc(x_55);
x_58 = lean_local_ctx_mk_local_decl(x_4, x_55, x_39, x_53, x_57);
x_59 = l_Lean_mkFVar(x_55);
x_60 = lean_array_push(x_5, x_59);
x_4 = x_58;
x_5 = x_60;
x_7 = x_41;
x_12 = x_56;
goto _start;
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_13 = x_62;
goto block_24;
}
block_24:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_5);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 1);
lean_dec(x_16);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_4);
if (x_2 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(x_1, x_14, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_6);
lean_inc(x_5);
x_18 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
if (x_2 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_22 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(x_1, x_14, x_5, x_6, x_21, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_5, x_6, x_21, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1;
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_9);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = 1;
x_17 = l_Array_empty___closed__1;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3(x_1, x_16, x_3, x_15, x_17, x_18, x_11, x_4, x_5, x_6, x_7, x_12);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = l_Lean_Expr_isForall(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = 1;
x_27 = l_Array_empty___closed__1;
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3(x_1, x_26, x_3, x_25, x_27, x_28, x_20, x_4, x_5, x_6, x_7, x_21);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_getExternConstArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_externAttr;
lean_inc(x_1);
x_11 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_10, x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_free_object(x_5);
x_16 = l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_ConstantInfo_type(x_17);
lean_dec(x_17);
x_20 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_21 = lean_st_mk_ref(x_20, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_getParamNamesImpl___closed__1;
x_26 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_22);
x_27 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2(x_25, x_19, x_24, x_26, x_22, x_2, x_3, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_11, 0, x_28);
lean_ctor_set(x_30, 0, x_11);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_11, 0, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_free_object(x_11);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_free_object(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_5, 0, x_45);
return x_5;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_free_object(x_5);
x_48 = l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_ConstantInfo_type(x_49);
lean_dec(x_49);
x_52 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_53 = lean_st_mk_ref(x_52, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_getParamNamesImpl___closed__1;
x_58 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_54);
x_59 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2(x_57, x_51, x_56, x_58, x_54, x_2, x_3, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_54, x_61);
lean_dec(x_54);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_69 = x_59;
} else {
 lean_dec_ref(x_59);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_48, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_73 = x_48;
} else {
 lean_dec_ref(x_48);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_47, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_76 = x_47;
} else {
 lean_dec_ref(x_47);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_5, 0, x_77);
return x_5;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_5, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_externAttr;
lean_inc(x_1);
x_82 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_81, x_80, x_1);
lean_dec(x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_86 = x_82;
} else {
 lean_dec_ref(x_82);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1(x_1, x_2, x_3, x_79);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_ConstantInfo_type(x_89);
lean_dec(x_89);
x_92 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_93 = lean_st_mk_ref(x_92, x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_97 = l_Lean_Meta_getParamNamesImpl___closed__1;
x_98 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_94);
x_99 = l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2(x_97, x_91, x_96, x_98, x_94, x_2, x_3, x_95);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_ref_get(x_94, x_101);
lean_dec(x_94);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_86;
}
lean_ctor_set(x_105, 0, x_100);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_94);
lean_dec(x_86);
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_109 = x_99;
} else {
 lean_dec_ref(x_99);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_86);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_ctor_get(x_88, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_88, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_113 = x_88;
} else {
 lean_dec_ref(x_88);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_86);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_ctor_get(x_87, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_116 = x_87;
} else {
 lean_dec_ref(x_87);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_79);
return x_118;
}
}
}
}
}
lean_object* l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_Lean_getExternConstArity___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__5(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImpl___main___at_Lean_getExternConstArity___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___at_Lean_getExternConstArity___spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* lean_get_extern_const_arity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_NameGenerator_Inhabited___closed__3;
x_5 = l_Lean_TraceState_Inhabited___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_st_mk_ref(x_6, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Environment_addAttribute___closed__1;
lean_inc(x_8);
x_11 = l_Lean_getExternConstArity(x_2, x_10, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_13);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_ProjFns(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_ExternAttr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ExternAttrData_inhabited___closed__1 = _init_l_Lean_ExternAttrData_inhabited___closed__1();
lean_mark_persistent(l_Lean_ExternAttrData_inhabited___closed__1);
l_Lean_ExternAttrData_inhabited = _init_l_Lean_ExternAttrData_inhabited();
lean_mark_persistent(l_Lean_ExternAttrData_inhabited);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6);
l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7 = _init_l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9);
l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10 = _init_l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10);
l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1 = _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__5___closed__1);
l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___closed__1 = _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___closed__1();
lean_mark_persistent(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__2___closed__1);
l_Lean_mkExternAttr___closed__1 = _init_l_Lean_mkExternAttr___closed__1();
lean_mark_persistent(l_Lean_mkExternAttr___closed__1);
l_Lean_mkExternAttr___closed__2 = _init_l_Lean_mkExternAttr___closed__2();
lean_mark_persistent(l_Lean_mkExternAttr___closed__2);
l_Lean_mkExternAttr___closed__3 = _init_l_Lean_mkExternAttr___closed__3();
lean_mark_persistent(l_Lean_mkExternAttr___closed__3);
l_Lean_mkExternAttr___closed__4 = _init_l_Lean_mkExternAttr___closed__4();
lean_mark_persistent(l_Lean_mkExternAttr___closed__4);
l_Lean_mkExternAttr___closed__5 = _init_l_Lean_mkExternAttr___closed__5();
lean_mark_persistent(l_Lean_mkExternAttr___closed__5);
res = l_Lean_mkExternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1 = _init_l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_14__forallTelescopeReducingAux___at_Lean_getExternConstArity___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
