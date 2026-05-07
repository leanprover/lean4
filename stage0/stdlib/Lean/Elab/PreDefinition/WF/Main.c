// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: public import Lean.Elab.PreDefinition.WF.PackMutual public import Lean.Elab.PreDefinition.WF.FloatRecApp public import Lean.Elab.PreDefinition.WF.Rel public import Lean.Elab.PreDefinition.WF.Fix public import Lean.Elab.PreDefinition.WF.Unfold public import Lean.Elab.PreDefinition.WF.Preprocess public import Lean.Elab.PreDefinition.WF.GuessLex
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "well-founded recursion cannot be used, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not take any (non-fixed) arguments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_wfRecursion___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_wfRecursion___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_wfRecursion___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "marking functions defined by well-founded recursion as `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` is not effective"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wfRel: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "wfRecursion: expected unary function type: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_wfRecursion___closed__2 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">> "};
static const lean_object* l_Lean_Elab_wfRecursion___closed__3 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__3_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__4;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " :=\n"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__5 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__5_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__6;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unaryPreDefProcessed:"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__7 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__7_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__8;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unaryPreDef:"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__9 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__9_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__10;
static const lean_ctor_object l_Lean_Elab_wfRecursion___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_wfRecursion___boxed__const__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 60, 146, 67, 170, 35, 9, 50)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 191, 24, 173, 99, 110, 250, 159)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(183, 176, 152, 199, 88, 244, 126, 231)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 192, 220, 42, 201, 36, 231, 139)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 8, 70, 241, 95, 177, 39, 230)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 164, 65, 123, 204, 166, 116, 237)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 212, 71, 249, 113, 26, 236, 1)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 192, 221, 228, 155, 175, 93, 246)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 119, 48, 4, 113, 111, 251, 171)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 104, 40, 162, 247, 89, 56, 248)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 159, 143, 175, 93, 190, 135, 30)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 178, 65, 214, 219, 44, 29, 26)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1197449596) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 70, 68, 25, 255, 132, 81, 38)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 173, 23, 241, 152, 14, 79, 23)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 207, 166, 163, 30, 74, 122, 49)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 76, 225, 120, 116, 96, 87, 123)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
v___x_7_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_6_);
lean_ctor_set(v___x_7_, 5, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object* v_env_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; lean_object* v_nextMacroScope_13_; lean_object* v_ngen_14_; lean_object* v_auxDeclNGen_15_; lean_object* v_traceState_16_; lean_object* v_messages_17_; lean_object* v_infoState_18_; lean_object* v_snapshotTasks_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_45_; 
v___x_12_ = lean_st_ref_take(v___y_10_);
v_nextMacroScope_13_ = lean_ctor_get(v___x_12_, 1);
v_ngen_14_ = lean_ctor_get(v___x_12_, 2);
v_auxDeclNGen_15_ = lean_ctor_get(v___x_12_, 3);
v_traceState_16_ = lean_ctor_get(v___x_12_, 4);
v_messages_17_ = lean_ctor_get(v___x_12_, 6);
v_infoState_18_ = lean_ctor_get(v___x_12_, 7);
v_snapshotTasks_19_ = lean_ctor_get(v___x_12_, 8);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; lean_object* v_unused_47_; 
v_unused_46_ = lean_ctor_get(v___x_12_, 5);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_47_);
v___x_21_ = v___x_12_;
v_isShared_22_ = v_isSharedCheck_45_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snapshotTasks_19_);
lean_inc(v_infoState_18_);
lean_inc(v_messages_17_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_15_);
lean_inc(v_ngen_14_);
lean_inc(v_nextMacroScope_13_);
lean_dec(v___x_12_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_45_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 5, v___x_23_);
lean_ctor_set(v___x_21_, 0, v_env_8_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_env_8_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_nextMacroScope_13_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_ngen_14_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_auxDeclNGen_15_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_traceState_16_);
lean_ctor_set(v_reuseFailAlloc_44_, 5, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_44_, 6, v_messages_17_);
lean_ctor_set(v_reuseFailAlloc_44_, 7, v_infoState_18_);
lean_ctor_set(v_reuseFailAlloc_44_, 8, v_snapshotTasks_19_);
v___x_25_ = v_reuseFailAlloc_44_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_mctx_28_; lean_object* v_zetaDeltaFVarIds_29_; lean_object* v_postponed_30_; lean_object* v_diag_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_42_; 
v___x_26_ = lean_st_ref_set(v___y_10_, v___x_25_);
v___x_27_ = lean_st_ref_take(v___y_9_);
v_mctx_28_ = lean_ctor_get(v___x_27_, 0);
v_zetaDeltaFVarIds_29_ = lean_ctor_get(v___x_27_, 2);
v_postponed_30_ = lean_ctor_get(v___x_27_, 3);
v_diag_31_ = lean_ctor_get(v___x_27_, 4);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_27_, 1);
lean_dec(v_unused_43_);
v___x_33_ = v___x_27_;
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_diag_31_);
lean_inc(v_postponed_30_);
lean_inc(v_zetaDeltaFVarIds_29_);
lean_inc(v_mctx_28_);
lean_dec(v___x_27_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_mctx_28_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v_zetaDeltaFVarIds_29_);
lean_ctor_set(v_reuseFailAlloc_41_, 3, v_postponed_30_);
lean_ctor_set(v_reuseFailAlloc_41_, 4, v_diag_31_);
v___x_37_ = v_reuseFailAlloc_41_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_st_ref_set(v___y_9_, v___x_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec(v___y_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_53_, v___y_57_, v___y_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object* v_k_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v_b_74_, lean_object* v_c_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc(v___y_77_);
lean_inc_ref(v___y_76_);
lean_inc(v___y_73_);
lean_inc_ref(v___y_72_);
v___x_81_ = lean_apply_9(v_k_71_, v_b_74_, v_c_75_, v___y_72_, v___y_73_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, lean_box(0));
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object* v_k_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v_b_85_, lean_object* v_c_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_82_, v___y_83_, v___y_84_, v_b_85_, v_c_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_type_93_, lean_object* v_maxFVars_x3f_94_, lean_object* v_k_95_, uint8_t v_cleanupAnnotations_96_, uint8_t v_whnfType_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; 
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_105_, 0, v_k_95_);
lean_closure_set(v___f_105_, 1, v___y_98_);
lean_closure_set(v___f_105_, 2, v___y_99_);
v___x_106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_93_, v_maxFVars_x3f_94_, v___f_105_, v_cleanupAnnotations_96_, v_whnfType_97_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_type_115_, lean_object* v_maxFVars_x3f_116_, lean_object* v_k_117_, lean_object* v_cleanupAnnotations_118_, lean_object* v_whnfType_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_127_; uint8_t v_whnfType_boxed_128_; lean_object* v_res_129_; 
v_cleanupAnnotations_boxed_127_ = lean_unbox(v_cleanupAnnotations_118_);
v_whnfType_boxed_128_ = lean_unbox(v_whnfType_119_);
v_res_129_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_115_, v_maxFVars_x3f_116_, v_k_117_, v_cleanupAnnotations_boxed_127_, v_whnfType_boxed_128_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_00_u03b1_130_, lean_object* v_type_131_, lean_object* v_maxFVars_x3f_132_, lean_object* v_k_133_, uint8_t v_cleanupAnnotations_134_, uint8_t v_whnfType_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_131_, v_maxFVars_x3f_132_, v_k_133_, v_cleanupAnnotations_134_, v_whnfType_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_00_u03b1_144_, lean_object* v_type_145_, lean_object* v_maxFVars_x3f_146_, lean_object* v_k_147_, lean_object* v_cleanupAnnotations_148_, lean_object* v_whnfType_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_157_; uint8_t v_whnfType_boxed_158_; lean_object* v_res_159_; 
v_cleanupAnnotations_boxed_157_ = lean_unbox(v_cleanupAnnotations_148_);
v_whnfType_boxed_158_ = lean_unbox(v_whnfType_149_);
v_res_159_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(v_00_u03b1_144_, v_type_145_, v_maxFVars_x3f_146_, v_k_147_, v_cleanupAnnotations_boxed_157_, v_whnfType_boxed_158_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_159_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(1);
v___x_161_ = l_Lean_MessageData_ofFormat(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2));
v___x_166_ = l_Lean_MessageData_ofFormat(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
return v_x_167_;
}
else
{
lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_192_; 
v_head_169_ = lean_ctor_get(v_x_168_, 0);
v_tail_170_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_192_ == 0)
{
v___x_172_ = v_x_168_;
v_isShared_173_ = v_isSharedCheck_192_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_tail_170_);
lean_inc(v_head_169_);
lean_dec(v_x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_192_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_before_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_190_; 
v_before_174_ = lean_ctor_get(v_head_169_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_head_169_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v_head_169_, 1);
lean_dec(v_unused_191_);
v___x_176_ = v_head_169_;
v_isShared_177_ = v_isSharedCheck_190_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_before_174_);
lean_dec(v_head_169_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_190_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 7);
lean_ctor_set(v___x_176_, 1, v___x_178_);
lean_ctor_set(v___x_176_, 0, v_x_167_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_x_167_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_189_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 7);
lean_ctor_set(v___x_172_, 1, v___x_181_);
lean_ctor_set(v___x_172_, 0, v___x_180_);
v___x_183_ = v___x_172_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_188_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = l_Lean_MessageData_ofSyntax(v_before_174_);
v___x_185_ = l_Lean_indentD(v___x_184_);
v___x_186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_183_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v_x_167_ = v___x_186_;
v_x_168_ = v_tail_170_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_opts_193_, lean_object* v_opt_194_){
_start:
{
lean_object* v_name_195_; lean_object* v_defValue_196_; lean_object* v_map_197_; lean_object* v___x_198_; 
v_name_195_ = lean_ctor_get(v_opt_194_, 0);
v_defValue_196_ = lean_ctor_get(v_opt_194_, 1);
v_map_197_ = lean_ctor_get(v_opts_193_, 0);
v___x_198_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_197_, v_name_195_);
if (lean_obj_tag(v___x_198_) == 0)
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v_defValue_196_);
return v___x_199_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_val_200_);
lean_dec_ref(v___x_198_);
if (lean_obj_tag(v_val_200_) == 1)
{
uint8_t v_v_201_; 
v_v_201_ = lean_ctor_get_uint8(v_val_200_, 0);
lean_dec_ref(v_val_200_);
return v_v_201_;
}
else
{
uint8_t v___x_202_; 
lean_dec(v_val_200_);
v___x_202_ = lean_unbox(v_defValue_196_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_203_, lean_object* v_opt_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_203_, v_opt_204_);
lean_dec_ref(v_opt_204_);
lean_dec_ref(v_opts_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_211_ = l_Lean_MessageData_ofFormat(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_212_, lean_object* v_macroStack_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_options_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_options_216_ = lean_ctor_get(v___y_214_, 2);
v___x_217_ = l_Lean_Elab_pp_macroStack;
v___x_218_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec(v_macroStack_213_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v_msgData_212_);
return v___x_219_;
}
else
{
if (lean_obj_tag(v_macroStack_213_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_msgData_212_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_after_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_237_; 
v_head_221_ = lean_ctor_get(v_macroStack_213_, 0);
lean_inc(v_head_221_);
v_after_222_ = lean_ctor_get(v_head_221_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_head_221_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_head_221_, 0);
lean_dec(v_unused_238_);
v___x_224_ = v_head_221_;
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_after_222_);
lean_dec(v_head_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 7);
lean_ctor_set(v___x_224_, 1, v___x_226_);
lean_ctor_set(v___x_224_, 0, v_msgData_212_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_msgData_212_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_236_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_msgData_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_229_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_MessageData_ofSyntax(v_after_222_);
v___x_232_ = l_Lean_indentD(v___x_231_);
v_msgData_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_233_, 0, v___x_230_);
lean_ctor_set(v_msgData_233_, 1, v___x_232_);
v___x_234_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_233_, v_macroStack_213_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_239_, lean_object* v_macroStack_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_239_, v_macroStack_240_, v___y_241_);
lean_dec_ref(v___y_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; lean_object* v_env_251_; lean_object* v___x_252_; lean_object* v_mctx_253_; lean_object* v_lctx_254_; lean_object* v_options_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_250_ = lean_st_ref_get(v___y_248_);
v_env_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc_ref(v_env_251_);
lean_dec(v___x_250_);
v___x_252_ = lean_st_ref_get(v___y_246_);
v_mctx_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc_ref(v_mctx_253_);
lean_dec(v___x_252_);
v_lctx_254_ = lean_ctor_get(v___y_245_, 2);
v_options_255_ = lean_ctor_get(v___y_247_, 2);
lean_inc_ref(v_options_255_);
lean_inc_ref(v_lctx_254_);
v___x_256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_256_, 0, v_env_251_);
lean_ctor_set(v___x_256_, 1, v_mctx_253_);
lean_ctor_set(v___x_256_, 2, v_lctx_254_);
lean_ctor_set(v___x_256_, 3, v_options_255_);
v___x_257_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_msgData_244_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_ref_274_; lean_object* v___x_275_; lean_object* v_a_276_; lean_object* v_macroStack_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v_ref_274_ = lean_ctor_get(v___y_271_, 5);
v___x_275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_266_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v_macroStack_277_ = lean_ctor_get(v___y_267_, 1);
v___x_278_ = l_Lean_Elab_getBetterRef(v_ref_274_, v_macroStack_277_);
lean_inc(v_macroStack_277_);
v___x_279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_276_, v_macroStack_277_, v___y_271_);
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_278_);
lean_ctor_set(v___x_284_, 1, v_a_280_);
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 1);
lean_ctor_set(v___x_282_, 0, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_as_304_, size_t v_sz_305_, size_t v_i_306_, lean_object* v_b_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_a_316_; uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_lt(v_i_306_, v_sz_305_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_b_307_);
return v___x_321_;
}
else
{
lean_object* v_array_322_; lean_object* v_start_323_; lean_object* v_stop_324_; uint8_t v___x_325_; 
v_array_322_ = lean_ctor_get(v_b_307_, 0);
v_start_323_ = lean_ctor_get(v_b_307_, 1);
v_stop_324_ = lean_ctor_get(v_b_307_, 2);
v___x_325_ = lean_nat_dec_lt(v_start_323_, v_stop_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_b_307_);
return v___x_326_;
}
else
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_355_; 
lean_inc(v_stop_324_);
lean_inc(v_start_323_);
lean_inc_ref(v_array_322_);
v_isSharedCheck_355_ = !lean_is_exclusive(v_b_307_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_356_ = lean_ctor_get(v_b_307_, 2);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_b_307_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_b_307_, 0);
lean_dec(v_unused_358_);
v___x_328_ = v_b_307_;
v_isShared_329_ = v_isSharedCheck_355_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_b_307_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_355_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v_a_330_ = lean_array_uget_borrowed(v_as_304_, v_i_306_);
v___x_331_ = lean_array_fget(v_array_322_, v_start_323_);
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_start_323_, v___x_332_);
lean_dec(v_start_323_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_array_322_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_stop_324_);
v___x_335_ = v_reuseFailAlloc_354_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_array_get_size(v_a_330_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_nat_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v___x_331_);
v_a_316_ = v___x_335_;
goto v___jp_315_;
}
else
{
lean_object* v_declName_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_declName_339_ = lean_ctor_get(v___x_331_, 3);
lean_inc(v_declName_339_);
lean_dec(v___x_331_);
v___x_340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1);
v___x_341_ = l_Lean_MessageData_ofName(v_declName_339_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_344_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_dec_ref(v___x_345_);
v_a_316_ = v___x_335_;
goto v___jp_315_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___x_335_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
}
}
v___jp_315_:
{
size_t v___x_317_; size_t v___x_318_; 
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_add(v_i_306_, v___x_317_);
v_i_306_ = v___x_318_;
v_b_307_ = v_a_316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_as_359_, lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_371_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_as_359_, v_sz_boxed_370_, v_i_boxed_371_, v_b_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_as_359_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_a_373_, lean_object* v_as_374_, lean_object* v_i_375_, lean_object* v_j_376_, lean_object* v_bs_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_zero_383_; uint8_t v_isZero_384_; 
v_zero_383_ = lean_unsigned_to_nat(0u);
v_isZero_384_ = lean_nat_dec_eq(v_i_375_, v_zero_383_);
if (v_isZero_384_ == 1)
{
lean_object* v___x_385_; 
lean_dec(v_j_376_);
lean_dec(v_i_375_);
lean_dec_ref(v_a_373_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_bs_377_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_array_fget_borrowed(v_as_374_, v_j_376_);
lean_inc(v___x_386_);
lean_inc(v_j_376_);
lean_inc_ref(v_a_373_);
v___x_387_ = l_Lean_Elab_WF_varyingVarNames(v_a_373_, v_j_376_, v___x_386_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v_one_389_; lean_object* v_n_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
v_one_389_ = lean_unsigned_to_nat(1u);
v_n_390_ = lean_nat_sub(v_i_375_, v_one_389_);
lean_dec(v_i_375_);
v___x_391_ = lean_nat_add(v_j_376_, v_one_389_);
lean_dec(v_j_376_);
v___x_392_ = lean_array_push(v_bs_377_, v_a_388_);
v_i_375_ = v_n_390_;
v_j_376_ = v___x_391_;
v_bs_377_ = v___x_392_;
goto _start;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v_bs_377_);
lean_dec(v_j_376_);
lean_dec(v_i_375_);
lean_dec_ref(v_a_373_);
v_a_394_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_387_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_387_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_a_402_, lean_object* v_as_403_, lean_object* v_i_404_, lean_object* v_j_405_, lean_object* v_bs_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_402_, v_as_403_, v_i_404_, v_j_405_, v_bs_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec_ref(v_as_403_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object* v_as_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_b_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_b_416_);
return v___x_421_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_423_; 
v_a_422_ = lean_array_uget_borrowed(v_as_413_, v_i_415_);
v___x_423_ = l_Lean_Elab_addAsAxiom___redArg(v_a_422_, v___y_417_, v___y_418_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_424_; size_t v___x_425_; size_t v___x_426_; 
lean_dec_ref(v___x_423_);
v___x_424_ = lean_box(0);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_415_, v___x_425_);
v_i_415_ = v___x_426_;
v_b_416_ = v___x_424_;
goto _start;
}
else
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_as_428_, lean_object* v_sz_429_, lean_object* v_i_430_, lean_object* v_b_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
size_t v_sz_boxed_435_; size_t v_i_boxed_436_; lean_object* v_res_437_; 
v_sz_boxed_435_ = lean_unbox_usize(v_sz_429_);
lean_dec(v_sz_429_);
v_i_boxed_436_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_428_, v_sz_boxed_435_, v_i_boxed_436_, v_b_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec_ref(v_as_428_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t v_sz_438_, size_t v_i_439_, lean_object* v_bs_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = lean_usize_dec_lt(v_i_439_, v_sz_438_);
if (v___x_441_ == 0)
{
return v_bs_440_;
}
else
{
lean_object* v_v_442_; lean_object* v_declName_443_; lean_object* v___x_444_; lean_object* v_bs_x27_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v_v_442_ = lean_array_uget_borrowed(v_bs_440_, v_i_439_);
v_declName_443_ = lean_ctor_get(v_v_442_, 3);
lean_inc(v_declName_443_);
v___x_444_ = lean_unsigned_to_nat(0u);
v_bs_x27_445_ = lean_array_uset(v_bs_440_, v_i_439_, v___x_444_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_439_, v___x_446_);
v___x_448_ = lean_array_uset(v_bs_x27_445_, v_i_439_, v_declName_443_);
v_i_439_ = v___x_447_;
v_bs_440_ = v___x_448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_bs_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_454_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_boxed_453_, v_i_boxed_454_, v_bs_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object* v_a_456_, lean_object* v___x_457_, size_t v_sz_458_, size_t v_i_459_, lean_object* v_bs_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_lt(v_i_459_, v_sz_458_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v___x_457_);
lean_dec_ref(v_a_456_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_bs_460_);
return v___x_465_;
}
else
{
lean_object* v_v_466_; lean_object* v_ref_467_; uint8_t v_kind_468_; lean_object* v_levelParams_469_; lean_object* v_modifiers_470_; lean_object* v_declName_471_; lean_object* v_binders_472_; lean_object* v_numSectionVars_473_; lean_object* v_type_474_; lean_object* v_value_475_; lean_object* v_termination_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_502_; 
v_v_466_ = lean_array_uget(v_bs_460_, v_i_459_);
v_ref_467_ = lean_ctor_get(v_v_466_, 0);
v_kind_468_ = lean_ctor_get_uint8(v_v_466_, sizeof(void*)*9);
v_levelParams_469_ = lean_ctor_get(v_v_466_, 1);
v_modifiers_470_ = lean_ctor_get(v_v_466_, 2);
v_declName_471_ = lean_ctor_get(v_v_466_, 3);
v_binders_472_ = lean_ctor_get(v_v_466_, 4);
v_numSectionVars_473_ = lean_ctor_get(v_v_466_, 5);
v_type_474_ = lean_ctor_get(v_v_466_, 6);
v_value_475_ = lean_ctor_get(v_v_466_, 7);
v_termination_476_ = lean_ctor_get(v_v_466_, 8);
v_isSharedCheck_502_ = !lean_is_exclusive(v_v_466_);
if (v_isSharedCheck_502_ == 0)
{
v___x_478_ = v_v_466_;
v_isShared_479_ = v_isSharedCheck_502_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_termination_476_);
lean_inc(v_value_475_);
lean_inc(v_type_474_);
lean_inc(v_numSectionVars_473_);
lean_inc(v_binders_472_);
lean_inc(v_declName_471_);
lean_inc(v_modifiers_470_);
lean_inc(v_levelParams_469_);
lean_inc(v_ref_467_);
lean_dec(v_v_466_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_502_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
size_t v_sz_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_sz_480_ = lean_array_size(v_a_456_);
v___x_481_ = ((size_t)0ULL);
lean_inc_ref(v_a_456_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_480_, v___x_481_, v_a_456_);
lean_inc(v___x_457_);
v___x_483_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_482_, v___x_457_, v_value_475_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; lean_object* v_bs_x27_486_; lean_object* v___x_488_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
v___x_485_ = lean_unsigned_to_nat(0u);
v_bs_x27_486_ = lean_array_uset(v_bs_460_, v_i_459_, v___x_485_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 7, v_a_484_);
v___x_488_ = v___x_478_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_ref_467_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_levelParams_469_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_modifiers_470_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_declName_471_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_binders_472_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_numSectionVars_473_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_type_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_a_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_termination_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*9, v_kind_468_);
v___x_488_ = v_reuseFailAlloc_493_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_459_, v___x_489_);
v___x_491_ = lean_array_uset(v_bs_x27_486_, v_i_459_, v___x_488_);
v_i_459_ = v___x_490_;
v_bs_460_ = v___x_491_;
goto _start;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_478_);
lean_dec_ref(v_termination_476_);
lean_dec_ref(v_type_474_);
lean_dec(v_numSectionVars_473_);
lean_dec(v_binders_472_);
lean_dec(v_declName_471_);
lean_dec_ref(v_modifiers_470_);
lean_dec(v_levelParams_469_);
lean_dec(v_ref_467_);
lean_dec_ref(v_bs_460_);
lean_dec(v___x_457_);
lean_dec_ref(v_a_456_);
v_a_494_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_483_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_483_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object* v_a_503_, lean_object* v___x_504_, lean_object* v_sz_505_, lean_object* v_i_506_, lean_object* v_bs_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_505_);
lean_dec(v_sz_505_);
v_i_boxed_512_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_503_, v___x_504_, v_sz_boxed_511_, v_i_boxed_512_, v_bs_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_514_, size_t v_sz_515_, size_t v___x_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_a_514_, v_sz_515_, v___x_516_, v___x_517_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v___x_527_; 
lean_dec_ref(v___x_526_);
lean_inc_ref(v_a_514_);
v___x_527_ = l_Lean_Elab_getFixedParamPerms(v_a_514_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_n(v_a_528_, 2);
lean_dec_ref(v___x_527_);
v___x_529_ = lean_array_get_size(v_a_514_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_532_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_528_, v_a_514_, v___x_529_, v___x_530_, v___x_531_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; size_t v_sz_535_; lean_object* v___x_536_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_532_);
lean_inc_ref(v_a_514_);
v___x_534_ = l_Array_toSubarray___redArg(v_a_514_, v___x_530_, v___x_529_);
v_sz_535_ = lean_array_size(v_a_533_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_533_, v_sz_535_, v___x_516_, v___x_534_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; lean_object* v_numSectionVars_538_; lean_object* v___x_539_; 
lean_dec_ref(v___x_536_);
v___x_537_ = lean_array_get_borrowed(v___x_518_, v_a_514_, v___x_530_);
v_numSectionVars_538_ = lean_ctor_get(v___x_537_, 5);
lean_inc(v_numSectionVars_538_);
lean_inc_ref(v_a_514_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_514_, v_numSectionVars_538_, v_sz_515_, v___x_516_, v_a_514_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
lean_inc(v_a_533_);
lean_inc(v_a_528_);
v___x_541_ = l_Lean_Elab_WF_packMutual(v_a_528_, v_a_533_, v_a_540_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_551_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_a_533_);
lean_ctor_set(v___x_546_, 1, v_a_542_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_528_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_547_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_a_533_);
lean_dec(v_a_528_);
v_a_552_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_541_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_541_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_533_);
lean_dec(v_a_528_);
v_a_560_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_539_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_539_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_a_533_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_514_);
v_a_568_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_536_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_536_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_a_528_);
lean_dec_ref(v_a_514_);
v_a_576_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_532_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_532_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v_a_514_);
v_a_584_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_527_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_527_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_a_514_);
v_a_592_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_526_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_526_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_600_, lean_object* v_sz_601_, lean_object* v___x_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v___x_46799__boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_601_);
lean_dec(v_sz_601_);
v___x_46799__boxed_613_ = lean_unbox_usize(v___x_602_);
lean_dec(v___x_602_);
v_res_614_ = l_Lean_Elab_wfRecursion___lam__0(v_a_600_, v_sz_boxed_612_, v___x_46799__boxed_613_, v___x_603_, v___x_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec_ref(v___x_604_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v___x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_options_626_; uint8_t v_hasTrace_627_; 
v_options_626_ = lean_ctor_get(v___y_623_, 2);
v_hasTrace_627_ = lean_ctor_get_uint8(v_options_626_, sizeof(void*)*1);
if (v_hasTrace_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___x_618_);
v___x_628_ = lean_box(v_hasTrace_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_inheritedTraceOptions_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_inheritedTraceOptions_630_ = lean_ctor_get(v___y_623_, 13);
v___x_631_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
v___x_632_ = l_Lean_Name_append(v___x_631_, v___x_618_);
v___x_633_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_630_, v_options_626_, v___x_632_);
lean_dec(v___x_632_);
v___x_634_ = lean_box(v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v___x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Elab_wfRecursion___lam__1(v___x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v_snd_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_645_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_ref_654_; uint8_t v_kind_655_; lean_object* v_levelParams_656_; lean_object* v_modifiers_657_; lean_object* v_declName_658_; lean_object* v_binders_659_; lean_object* v_numSectionVars_660_; lean_object* v_type_661_; lean_object* v_value_662_; lean_object* v_termination_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v___x_653_);
v_ref_654_ = lean_ctor_get(v_snd_645_, 0);
v_kind_655_ = lean_ctor_get_uint8(v_snd_645_, sizeof(void*)*9);
v_levelParams_656_ = lean_ctor_get(v_snd_645_, 1);
v_modifiers_657_ = lean_ctor_get(v_snd_645_, 2);
v_declName_658_ = lean_ctor_get(v_snd_645_, 3);
v_binders_659_ = lean_ctor_get(v_snd_645_, 4);
v_numSectionVars_660_ = lean_ctor_get(v_snd_645_, 5);
v_type_661_ = lean_ctor_get(v_snd_645_, 6);
v_value_662_ = lean_ctor_get(v_snd_645_, 7);
v_termination_663_ = lean_ctor_get(v_snd_645_, 8);
v_isSharedCheck_689_ = !lean_is_exclusive(v_snd_645_);
if (v_isSharedCheck_689_ == 0)
{
v___x_665_ = v_snd_645_;
v_isShared_666_ = v_isSharedCheck_689_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_termination_663_);
lean_inc(v_value_662_);
lean_inc(v_type_661_);
lean_inc(v_numSectionVars_660_);
lean_inc(v_binders_659_);
lean_inc(v_declName_658_);
lean_inc(v_modifiers_657_);
lean_inc(v_levelParams_656_);
lean_inc(v_ref_654_);
lean_dec(v_snd_645_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_689_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Elab_WF_preprocess(v_value_662_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_680_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_680_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_expr_672_; lean_object* v___x_674_; 
v_expr_672_ = lean_ctor_get(v_a_668_, 0);
lean_inc_ref(v_expr_672_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 7, v_expr_672_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_ref_654_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_levelParams_656_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_modifiers_657_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_declName_658_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_binders_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 5, v_numSectionVars_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 6, v_type_661_);
lean_ctor_set(v_reuseFailAlloc_679_, 7, v_expr_672_);
lean_ctor_set(v_reuseFailAlloc_679_, 8, v_termination_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_679_, sizeof(void*)*9, v_kind_655_);
v___x_674_ = v_reuseFailAlloc_679_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_a_668_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_675_);
v___x_677_ = v___x_670_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_del_object(v___x_665_);
lean_dec_ref(v_termination_663_);
lean_dec_ref(v_type_661_);
lean_dec(v_numSectionVars_660_);
lean_dec(v_binders_659_);
lean_dec(v_declName_658_);
lean_dec_ref(v_modifiers_657_);
lean_dec(v_levelParams_656_);
lean_dec(v_ref_654_);
v_a_681_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_667_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_667_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v_snd_645_);
v_a_690_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_653_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_653_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v_snd_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Elab_wfRecursion___lam__2(v_snd_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_706_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v___y_714_, uint8_t v_suppressElabErrors_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 1)
{
lean_object* v_pre_717_; 
v_pre_717_ = lean_ctor_get(v_x_716_, 0);
switch(lean_obj_tag(v_pre_717_))
{
case 1:
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_pre_717_, 0);
switch(lean_obj_tag(v_pre_718_))
{
case 0:
{
lean_object* v_str_719_; lean_object* v_str_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_str_719_ = lean_ctor_get(v_x_716_, 1);
v_str_720_ = lean_ctor_get(v_pre_717_, 1);
v___x_721_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_722_ = lean_string_dec_eq(v_str_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_724_ = lean_string_dec_eq(v_str_720_, v___x_723_);
if (v___x_724_ == 0)
{
return v___y_714_;
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_726_ = lean_string_dec_eq(v_str_719_, v___x_725_);
if (v___x_726_ == 0)
{
return v___y_714_;
}
else
{
return v_suppressElabErrors_715_;
}
}
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_728_ = lean_string_dec_eq(v_str_719_, v___x_727_);
if (v___x_728_ == 0)
{
return v___y_714_;
}
else
{
return v_suppressElabErrors_715_;
}
}
}
case 1:
{
lean_object* v_pre_729_; 
v_pre_729_ = lean_ctor_get(v_pre_718_, 0);
if (lean_obj_tag(v_pre_729_) == 0)
{
lean_object* v_str_730_; lean_object* v_str_731_; lean_object* v_str_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_str_730_ = lean_ctor_get(v_x_716_, 1);
v_str_731_ = lean_ctor_get(v_pre_717_, 1);
v_str_732_ = lean_ctor_get(v_pre_718_, 1);
v___x_733_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_734_ = lean_string_dec_eq(v_str_732_, v___x_733_);
if (v___x_734_ == 0)
{
return v___y_714_;
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_736_ = lean_string_dec_eq(v_str_731_, v___x_735_);
if (v___x_736_ == 0)
{
return v___y_714_;
}
else
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_738_ = lean_string_dec_eq(v_str_730_, v___x_737_);
if (v___x_738_ == 0)
{
return v___y_714_;
}
else
{
return v_suppressElabErrors_715_;
}
}
}
}
else
{
return v___y_714_;
}
}
default: 
{
return v___y_714_;
}
}
}
case 0:
{
lean_object* v_str_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_str_739_ = lean_ctor_get(v_x_716_, 1);
v___x_740_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__0));
v___x_741_ = lean_string_dec_eq(v_str_739_, v___x_740_);
if (v___x_741_ == 0)
{
return v___y_714_;
}
else
{
return v_suppressElabErrors_715_;
}
}
default: 
{
return v___y_714_;
}
}
}
else
{
return v___y_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v___y_742_, lean_object* v_suppressElabErrors_743_, lean_object* v_x_744_){
_start:
{
uint8_t v___y_47131__boxed_745_; uint8_t v_suppressElabErrors_boxed_746_; uint8_t v_res_747_; lean_object* v_r_748_; 
v___y_47131__boxed_745_ = lean_unbox(v___y_742_);
v_suppressElabErrors_boxed_746_ = lean_unbox(v_suppressElabErrors_743_);
v_res_747_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v___y_47131__boxed_745_, v_suppressElabErrors_boxed_746_, v_x_744_);
lean_dec(v_x_744_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_750_, lean_object* v_msgData_751_, uint8_t v_severity_752_, uint8_t v_isSilent_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; uint8_t v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_796_; uint8_t v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_821_; uint8_t v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v___y_828_; lean_object* v___y_832_; uint8_t v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; uint8_t v___y_837_; uint8_t v___y_838_; uint8_t v___x_843_; uint8_t v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___y_850_; uint8_t v___y_851_; uint8_t v___y_853_; uint8_t v___x_868_; 
v___x_843_ = 2;
v___x_868_ = l_Lean_instBEqMessageSeverity_beq(v_severity_752_, v___x_843_);
if (v___x_868_ == 0)
{
v___y_853_ = v___x_868_;
goto v___jp_852_;
}
else
{
uint8_t v___x_869_; 
lean_inc_ref(v_msgData_751_);
v___x_869_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_751_);
v___y_853_ = v___x_869_;
goto v___jp_852_;
}
v___jp_759_:
{
lean_object* v___x_769_; lean_object* v_currNamespace_770_; lean_object* v_openDecls_771_; lean_object* v_env_772_; lean_object* v_nextMacroScope_773_; lean_object* v_ngen_774_; lean_object* v_auxDeclNGen_775_; lean_object* v_traceState_776_; lean_object* v_cache_777_; lean_object* v_messages_778_; lean_object* v_infoState_779_; lean_object* v_snapshotTasks_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_794_; 
v___x_769_ = lean_st_ref_take(v___y_768_);
v_currNamespace_770_ = lean_ctor_get(v___y_767_, 6);
v_openDecls_771_ = lean_ctor_get(v___y_767_, 7);
v_env_772_ = lean_ctor_get(v___x_769_, 0);
v_nextMacroScope_773_ = lean_ctor_get(v___x_769_, 1);
v_ngen_774_ = lean_ctor_get(v___x_769_, 2);
v_auxDeclNGen_775_ = lean_ctor_get(v___x_769_, 3);
v_traceState_776_ = lean_ctor_get(v___x_769_, 4);
v_cache_777_ = lean_ctor_get(v___x_769_, 5);
v_messages_778_ = lean_ctor_get(v___x_769_, 6);
v_infoState_779_ = lean_ctor_get(v___x_769_, 7);
v_snapshotTasks_780_ = lean_ctor_get(v___x_769_, 8);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_794_ == 0)
{
v___x_782_ = v___x_769_;
v_isShared_783_ = v_isSharedCheck_794_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snapshotTasks_780_);
lean_inc(v_infoState_779_);
lean_inc(v_messages_778_);
lean_inc(v_cache_777_);
lean_inc(v_traceState_776_);
lean_inc(v_auxDeclNGen_775_);
lean_inc(v_ngen_774_);
lean_inc(v_nextMacroScope_773_);
lean_inc(v_env_772_);
lean_dec(v___x_769_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_794_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_inc(v_openDecls_771_);
lean_inc(v_currNamespace_770_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_currNamespace_770_);
lean_ctor_set(v___x_784_, 1, v_openDecls_771_);
v___x_785_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___y_761_);
lean_inc_ref(v___y_762_);
lean_inc_ref(v___y_764_);
v___x_786_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_786_, 0, v___y_764_);
lean_ctor_set(v___x_786_, 1, v___y_760_);
lean_ctor_set(v___x_786_, 2, v___y_766_);
lean_ctor_set(v___x_786_, 3, v___y_762_);
lean_ctor_set(v___x_786_, 4, v___x_785_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*5, v___y_765_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*5 + 1, v___y_763_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*5 + 2, v_isSilent_753_);
v___x_787_ = l_Lean_MessageLog_add(v___x_786_, v_messages_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 6, v___x_787_);
v___x_789_ = v___x_782_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_env_772_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_nextMacroScope_773_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_ngen_774_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_auxDeclNGen_775_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_traceState_776_);
lean_ctor_set(v_reuseFailAlloc_793_, 5, v_cache_777_);
lean_ctor_set(v_reuseFailAlloc_793_, 6, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_793_, 7, v_infoState_779_);
lean_ctor_set(v_reuseFailAlloc_793_, 8, v_snapshotTasks_780_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_st_ref_set(v___y_768_, v___x_789_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
v___jp_795_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_819_; 
v___x_804_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_751_);
v___x_805_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_804_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_819_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_819_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_819_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_inc_ref_n(v___y_798_, 2);
v___x_810_ = l_Lean_FileMap_toPosition(v___y_798_, v___y_802_);
lean_dec(v___y_802_);
v___x_811_ = l_Lean_FileMap_toPosition(v___y_798_, v___y_803_);
lean_dec(v___y_803_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_797_ == 0)
{
lean_del_object(v___x_808_);
lean_dec_ref(v___y_796_);
v___y_760_ = v___x_810_;
v___y_761_ = v_a_806_;
v___y_762_ = v___x_813_;
v___y_763_ = v___y_799_;
v___y_764_ = v___y_800_;
v___y_765_ = v___y_801_;
v___y_766_ = v___x_812_;
v___y_767_ = v___y_756_;
v___y_768_ = v___y_757_;
goto v___jp_759_;
}
else
{
uint8_t v___x_814_; 
lean_inc(v_a_806_);
v___x_814_ = l_Lean_MessageData_hasTag(v___y_796_, v_a_806_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v___x_812_);
lean_dec_ref(v___x_810_);
lean_dec(v_a_806_);
v___x_815_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_815_);
v___x_817_ = v___x_808_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_del_object(v___x_808_);
v___y_760_ = v___x_810_;
v___y_761_ = v_a_806_;
v___y_762_ = v___x_813_;
v___y_763_ = v___y_799_;
v___y_764_ = v___y_800_;
v___y_765_ = v___y_801_;
v___y_766_ = v___x_812_;
v___y_767_ = v___y_756_;
v___y_768_ = v___y_757_;
goto v___jp_759_;
}
}
}
}
v___jp_820_:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Syntax_getTailPos_x3f(v___y_824_, v___y_827_);
lean_dec(v___y_824_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_inc(v___y_828_);
v___y_796_ = v___y_821_;
v___y_797_ = v___y_822_;
v___y_798_ = v___y_823_;
v___y_799_ = v___y_825_;
v___y_800_ = v___y_826_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_828_;
v___y_803_ = v___y_828_;
goto v___jp_795_;
}
else
{
lean_object* v_val_830_; 
v_val_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_830_);
lean_dec_ref(v___x_829_);
v___y_796_ = v___y_821_;
v___y_797_ = v___y_822_;
v___y_798_ = v___y_823_;
v___y_799_ = v___y_825_;
v___y_800_ = v___y_826_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_828_;
v___y_803_ = v_val_830_;
goto v___jp_795_;
}
}
v___jp_831_:
{
lean_object* v_ref_839_; lean_object* v___x_840_; 
v_ref_839_ = l_Lean_replaceRef(v_ref_750_, v___y_836_);
v___x_840_ = l_Lean_Syntax_getPos_x3f(v_ref_839_, v___y_837_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___y_821_ = v___y_832_;
v___y_822_ = v___y_833_;
v___y_823_ = v___y_834_;
v___y_824_ = v_ref_839_;
v___y_825_ = v___y_838_;
v___y_826_ = v___y_835_;
v___y_827_ = v___y_837_;
v___y_828_ = v___x_841_;
goto v___jp_820_;
}
else
{
lean_object* v_val_842_; 
v_val_842_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_842_);
lean_dec_ref(v___x_840_);
v___y_821_ = v___y_832_;
v___y_822_ = v___y_833_;
v___y_823_ = v___y_834_;
v___y_824_ = v_ref_839_;
v___y_825_ = v___y_838_;
v___y_826_ = v___y_835_;
v___y_827_ = v___y_837_;
v___y_828_ = v_val_842_;
goto v___jp_820_;
}
}
v___jp_844_:
{
if (v___y_851_ == 0)
{
v___y_832_ = v___y_847_;
v___y_833_ = v___y_845_;
v___y_834_ = v___y_846_;
v___y_835_ = v___y_848_;
v___y_836_ = v___y_849_;
v___y_837_ = v___y_850_;
v___y_838_ = v_severity_752_;
goto v___jp_831_;
}
else
{
v___y_832_ = v___y_847_;
v___y_833_ = v___y_845_;
v___y_834_ = v___y_846_;
v___y_835_ = v___y_848_;
v___y_836_ = v___y_849_;
v___y_837_ = v___y_850_;
v___y_838_ = v___x_843_;
goto v___jp_831_;
}
}
v___jp_852_:
{
if (v___y_853_ == 0)
{
lean_object* v_fileName_854_; lean_object* v_fileMap_855_; lean_object* v_options_856_; lean_object* v_ref_857_; uint8_t v_suppressElabErrors_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___f_861_; uint8_t v___x_862_; uint8_t v___x_863_; 
v_fileName_854_ = lean_ctor_get(v___y_756_, 0);
v_fileMap_855_ = lean_ctor_get(v___y_756_, 1);
v_options_856_ = lean_ctor_get(v___y_756_, 2);
v_ref_857_ = lean_ctor_get(v___y_756_, 5);
v_suppressElabErrors_858_ = lean_ctor_get_uint8(v___y_756_, sizeof(void*)*14 + 1);
v___x_859_ = lean_box(v___y_853_);
v___x_860_ = lean_box(v_suppressElabErrors_858_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_861_, 0, v___x_859_);
lean_closure_set(v___f_861_, 1, v___x_860_);
v___x_862_ = 1;
v___x_863_ = l_Lean_instBEqMessageSeverity_beq(v_severity_752_, v___x_862_);
if (v___x_863_ == 0)
{
v___y_845_ = v_suppressElabErrors_858_;
v___y_846_ = v_fileMap_855_;
v___y_847_ = v___f_861_;
v___y_848_ = v_fileName_854_;
v___y_849_ = v_ref_857_;
v___y_850_ = v___y_853_;
v___y_851_ = v___x_863_;
goto v___jp_844_;
}
else
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = l_Lean_warningAsError;
v___x_865_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_856_, v___x_864_);
v___y_845_ = v_suppressElabErrors_858_;
v___y_846_ = v_fileMap_855_;
v___y_847_ = v___f_861_;
v___y_848_ = v_fileName_854_;
v___y_849_ = v_ref_857_;
v___y_850_ = v___y_853_;
v___y_851_ = v___x_865_;
goto v___jp_844_;
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref(v_msgData_751_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_870_, lean_object* v_msgData_871_, lean_object* v_severity_872_, lean_object* v_isSilent_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_severity_boxed_879_; uint8_t v_isSilent_boxed_880_; lean_object* v_res_881_; 
v_severity_boxed_879_ = lean_unbox(v_severity_872_);
v_isSilent_boxed_880_ = lean_unbox(v_isSilent_873_);
v_res_881_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_870_, v_msgData_871_, v_severity_boxed_879_, v_isSilent_boxed_880_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v_ref_870_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_882_, lean_object* v_msgData_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; 
v___x_891_ = 1;
v___x_892_ = 0;
v___x_893_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_882_, v_msgData_883_, v___x_891_, v___x_892_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_894_, lean_object* v_msgData_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_894_, v_msgData_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v_ref_894_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v_as_912_, size_t v_i_913_, size_t v_stop_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_a_924_; uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_eq(v_i_913_, v_stop_914_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v_name_930_; lean_object* v_stx_931_; uint8_t v___y_933_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_929_ = lean_array_uget_borrowed(v_as_912_, v_i_913_);
v_name_930_ = lean_ctor_get(v___x_929_, 0);
v_stx_931_ = lean_ctor_get(v___x_929_, 1);
v___x_943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_944_ = lean_name_eq(v_name_930_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_946_ = lean_name_eq(v_name_930_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_box(0);
v_a_924_ = v___x_947_;
goto v___jp_923_;
}
else
{
v___y_933_ = v___x_946_;
goto v___jp_932_;
}
}
else
{
v___y_933_ = v___x_944_;
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_930_);
v___x_935_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_930_, v___y_933_);
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
lean_dec_ref(v___x_935_);
v___x_937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
v___x_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = l_Lean_MessageData_ofFormat(v___x_939_);
v___x_941_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_931_, v___x_940_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v___x_941_);
v_a_924_ = v_a_942_;
goto v___jp_923_;
}
else
{
return v___x_941_;
}
}
}
else
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_b_915_);
return v___x_948_;
}
v___jp_923_:
{
size_t v___x_925_; size_t v___x_926_; 
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_913_, v___x_925_);
v_i_913_ = v___x_926_;
v_b_915_ = v_a_924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v_as_949_, lean_object* v_i_950_, lean_object* v_stop_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_i_boxed_960_; size_t v_stop_boxed_961_; lean_object* v_res_962_; 
v_i_boxed_960_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_951_);
lean_dec(v_stop_951_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_as_949_, v_i_boxed_960_, v_stop_boxed_961_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_as_949_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v_as_963_, size_t v_i_964_, size_t v_stop_965_, lean_object* v_b_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_a_975_; lean_object* v___y_980_; uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_eq(v_i_964_, v_stop_965_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_modifiers_984_; lean_object* v_attrs_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_983_ = lean_array_uget_borrowed(v_as_963_, v_i_964_);
v_modifiers_984_ = lean_ctor_get(v___x_983_, 2);
v_attrs_985_ = lean_ctor_get(v_modifiers_984_, 2);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_array_get_size(v_attrs_985_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_989_ == 0)
{
v_a_975_ = v___x_988_;
goto v___jp_974_;
}
else
{
uint8_t v___x_990_; 
v___x_990_ = lean_nat_dec_le(v___x_987_, v___x_987_);
if (v___x_990_ == 0)
{
if (v___x_989_ == 0)
{
v_a_975_ = v___x_988_;
goto v___jp_974_;
}
else
{
size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_of_nat(v___x_987_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_985_, v___x_991_, v___x_992_, v___x_988_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
v___y_980_ = v___x_993_;
goto v___jp_979_;
}
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_of_nat(v___x_987_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_985_, v___x_994_, v___x_995_, v___x_988_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
v___y_980_ = v___x_996_;
goto v___jp_979_;
}
}
}
else
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_b_966_);
return v___x_997_;
}
v___jp_974_:
{
size_t v___x_976_; size_t v___x_977_; 
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_add(v_i_964_, v___x_976_);
v_i_964_ = v___x_977_;
v_b_966_ = v_a_975_;
goto _start;
}
v___jp_979_:
{
if (lean_obj_tag(v___y_980_) == 0)
{
lean_object* v_a_981_; 
v_a_981_ = lean_ctor_get(v___y_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___y_980_);
v_a_975_ = v_a_981_;
goto v___jp_974_;
}
else
{
return v___y_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v_as_998_, lean_object* v_i_999_, lean_object* v_stop_1000_, lean_object* v_b_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
size_t v_i_boxed_1009_; size_t v_stop_boxed_1010_; lean_object* v_res_1011_; 
v_i_boxed_1009_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_stop_boxed_1010_ = lean_unbox_usize(v_stop_1000_);
lean_dec(v_stop_1000_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_as_998_, v_i_boxed_1009_, v_stop_boxed_1010_, v_b_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_as_998_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1012_, size_t v_i_1013_, lean_object* v_bs_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_usize_dec_lt(v_i_1013_, v_sz_1012_);
if (v___x_1015_ == 0)
{
return v_bs_1014_;
}
else
{
lean_object* v_v_1016_; lean_object* v_termination_1017_; lean_object* v_decreasingBy_x3f_1018_; lean_object* v___x_1019_; lean_object* v_bs_x27_1020_; size_t v___x_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v_v_1016_ = lean_array_uget_borrowed(v_bs_1014_, v_i_1013_);
v_termination_1017_ = lean_ctor_get(v_v_1016_, 8);
v_decreasingBy_x3f_1018_ = lean_ctor_get(v_termination_1017_, 4);
lean_inc(v_decreasingBy_x3f_1018_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v_bs_x27_1020_ = lean_array_uset(v_bs_1014_, v_i_1013_, v___x_1019_);
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_add(v_i_1013_, v___x_1021_);
v___x_1023_ = lean_array_uset(v_bs_x27_1020_, v_i_1013_, v_decreasingBy_x3f_1018_);
v_i_1013_ = v___x_1022_;
v_bs_1014_ = v___x_1023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_bs_1027_){
_start:
{
size_t v_sz_boxed_1028_; size_t v_i_boxed_1029_; lean_object* v_res_1030_; 
v_sz_boxed_1028_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1029_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1028_, v_i_boxed_1029_, v_bs_1027_);
return v_res_1030_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1031_; double v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_float_of_nat(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1035_, lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_ref_1042_; lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1088_; 
v_ref_1042_ = lean_ctor_get(v___y_1039_, 5);
v___x_1043_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1088_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1088_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v_traceState_1049_; lean_object* v_env_1050_; lean_object* v_nextMacroScope_1051_; lean_object* v_ngen_1052_; lean_object* v_auxDeclNGen_1053_; lean_object* v_cache_1054_; lean_object* v_messages_1055_; lean_object* v_infoState_1056_; lean_object* v_snapshotTasks_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1087_; 
v___x_1048_ = lean_st_ref_take(v___y_1040_);
v_traceState_1049_ = lean_ctor_get(v___x_1048_, 4);
v_env_1050_ = lean_ctor_get(v___x_1048_, 0);
v_nextMacroScope_1051_ = lean_ctor_get(v___x_1048_, 1);
v_ngen_1052_ = lean_ctor_get(v___x_1048_, 2);
v_auxDeclNGen_1053_ = lean_ctor_get(v___x_1048_, 3);
v_cache_1054_ = lean_ctor_get(v___x_1048_, 5);
v_messages_1055_ = lean_ctor_get(v___x_1048_, 6);
v_infoState_1056_ = lean_ctor_get(v___x_1048_, 7);
v_snapshotTasks_1057_ = lean_ctor_get(v___x_1048_, 8);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1059_ = v___x_1048_;
v_isShared_1060_ = v_isSharedCheck_1087_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snapshotTasks_1057_);
lean_inc(v_infoState_1056_);
lean_inc(v_messages_1055_);
lean_inc(v_cache_1054_);
lean_inc(v_traceState_1049_);
lean_inc(v_auxDeclNGen_1053_);
lean_inc(v_ngen_1052_);
lean_inc(v_nextMacroScope_1051_);
lean_inc(v_env_1050_);
lean_dec(v___x_1048_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1087_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
uint64_t v_tid_1061_; lean_object* v_traces_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1086_; 
v_tid_1061_ = lean_ctor_get_uint64(v_traceState_1049_, sizeof(void*)*1);
v_traces_1062_ = lean_ctor_get(v_traceState_1049_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_traceState_1049_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1064_ = v_traceState_1049_;
v_isShared_1065_ = v_isSharedCheck_1086_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_traces_1062_);
lean_dec(v_traceState_1049_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1086_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; double v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1068_ = 0;
v___x_1069_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1070_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1070_, 0, v_cls_1035_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set_float(v___x_1070_, sizeof(void*)*3, v___x_1067_);
lean_ctor_set_float(v___x_1070_, sizeof(void*)*3 + 8, v___x_1067_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*3 + 16, v___x_1068_);
v___x_1071_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1072_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v_a_1044_);
lean_ctor_set(v___x_1072_, 2, v___x_1071_);
lean_inc(v_ref_1042_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_ref_1042_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_PersistentArray_push___redArg(v_traces_1062_, v___x_1073_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1074_);
v___x_1076_ = v___x_1064_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1074_);
lean_ctor_set_uint64(v_reuseFailAlloc_1085_, sizeof(void*)*1, v_tid_1061_);
v___x_1076_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v___x_1076_);
v___x_1078_ = v___x_1059_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_env_1050_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_nextMacroScope_1051_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_ngen_1052_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_auxDeclNGen_1053_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1084_, 5, v_cache_1054_);
lean_ctor_set(v_reuseFailAlloc_1084_, 6, v_messages_1055_);
lean_ctor_set(v_reuseFailAlloc_1084_, 7, v_infoState_1056_);
lean_ctor_set(v_reuseFailAlloc_1084_, 8, v_snapshotTasks_1057_);
v___x_1078_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = lean_st_ref_set(v___y_1040_, v___x_1078_);
v___x_1080_ = lean_box(0);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1080_);
v___x_1082_ = v___x_1046_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1089_, lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1089_, v_msg_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1100_, lean_object* v_snd_1101_, size_t v_sz_1102_, size_t v___x_1103_, lean_object* v_a_1104_, lean_object* v_fixedArgs_1105_, lean_object* v_fst_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v_wfRel_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v_a_1126_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v_options_1275_; uint8_t v_hasTrace_1276_; 
v_options_1275_ = lean_ctor_get(v___y_1115_, 2);
v_hasTrace_1276_ = lean_ctor_get_uint8(v_options_1275_, sizeof(void*)*1);
if (v_hasTrace_1276_ == 0)
{
lean_dec(v___x_1109_);
v___y_1251_ = v___y_1111_;
v___y_1252_ = v___y_1112_;
v___y_1253_ = v___y_1113_;
v___y_1254_ = v___y_1114_;
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
goto v___jp_1250_;
}
else
{
lean_object* v_inheritedTraceOptions_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_inheritedTraceOptions_1277_ = lean_ctor_get(v___y_1115_, 13);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
lean_inc(v___x_1109_);
v___x_1279_ = l_Lean_Name_append(v___x_1278_, v___x_1109_);
v___x_1280_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1277_, v_options_1275_, v___x_1279_);
lean_dec(v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec(v___x_1109_);
v___y_1251_ = v___y_1111_;
v___y_1252_ = v___y_1112_;
v___y_1253_ = v___y_1113_;
v___y_1254_ = v___y_1114_;
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1110_);
v___x_1282_ = l_Lean_MessageData_ofExpr(v_wfRel_1110_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1109_, v___x_1283_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref(v___x_1284_);
v___y_1251_ = v___y_1111_;
v___y_1252_ = v___y_1112_;
v___y_1253_ = v___y_1113_;
v___y_1254_ = v___y_1114_;
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_wfRel_1110_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_fst_1106_);
lean_dec_ref(v_fixedArgs_1105_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_fst_1100_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
v___jp_1118_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v___x_1127_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1123_, v___y_1122_, v___y_1124_);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1127_, 0);
lean_dec(v_unused_1135_);
v___x_1129_ = v___x_1127_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_dec(v___x_1127_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 1);
lean_ctor_set(v___x_1129_, 0, v_a_1126_);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1126_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
v___jp_1136_:
{
if (lean_obj_tag(v___y_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_env_1148_; lean_object* v___x_1149_; 
v_a_1145_ = lean_ctor_get(v___y_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref(v___y_1144_);
v___x_1146_ = lean_st_ref_get(v___y_1142_);
v___x_1147_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1141_, v___y_1140_, v___y_1142_);
lean_dec_ref(v___x_1147_);
v_env_1148_ = lean_ctor_get(v___x_1146_, 0);
lean_inc_ref_n(v_env_1148_, 2);
lean_dec(v___x_1146_);
v___x_1149_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1148_, v_a_1145_, v___y_1143_, v___y_1142_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1209_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1209_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1209_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v_env_1155_; lean_object* v_nextMacroScope_1156_; lean_object* v_ngen_1157_; lean_object* v_auxDeclNGen_1158_; lean_object* v_traceState_1159_; lean_object* v_messages_1160_; lean_object* v_infoState_1161_; lean_object* v_snapshotTasks_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1207_; 
v___x_1154_ = lean_st_ref_take(v___y_1142_);
v_env_1155_ = lean_ctor_get(v___x_1154_, 0);
v_nextMacroScope_1156_ = lean_ctor_get(v___x_1154_, 1);
v_ngen_1157_ = lean_ctor_get(v___x_1154_, 2);
v_auxDeclNGen_1158_ = lean_ctor_get(v___x_1154_, 3);
v_traceState_1159_ = lean_ctor_get(v___x_1154_, 4);
v_messages_1160_ = lean_ctor_get(v___x_1154_, 6);
v_infoState_1161_ = lean_ctor_get(v___x_1154_, 7);
v_snapshotTasks_1162_ = lean_ctor_get(v___x_1154_, 8);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1154_, 5);
lean_dec(v_unused_1208_);
v___x_1164_ = v___x_1154_;
v_isShared_1165_ = v_isSharedCheck_1207_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snapshotTasks_1162_);
lean_inc(v_infoState_1161_);
lean_inc(v_messages_1160_);
lean_inc(v_traceState_1159_);
lean_inc(v_auxDeclNGen_1158_);
lean_inc(v_ngen_1157_);
lean_inc(v_nextMacroScope_1156_);
lean_inc(v_env_1155_);
lean_dec(v___x_1154_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1207_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = l_Lean_copyExtraModUses(v_env_1148_, v_env_1155_);
v___x_1167_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 5, v___x_1167_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_nextMacroScope_1156_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_ngen_1157_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_auxDeclNGen_1158_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_traceState_1159_);
lean_ctor_set(v_reuseFailAlloc_1206_, 5, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_messages_1160_);
lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_infoState_1161_);
lean_ctor_set(v_reuseFailAlloc_1206_, 8, v_snapshotTasks_1162_);
v___x_1169_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_mctx_1172_; lean_object* v_zetaDeltaFVarIds_1173_; lean_object* v_postponed_1174_; lean_object* v_diag_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1204_; 
v___x_1170_ = lean_st_ref_set(v___y_1142_, v___x_1169_);
v___x_1171_ = lean_st_ref_take(v___y_1140_);
v_mctx_1172_ = lean_ctor_get(v___x_1171_, 0);
v_zetaDeltaFVarIds_1173_ = lean_ctor_get(v___x_1171_, 2);
v_postponed_1174_ = lean_ctor_get(v___x_1171_, 3);
v_diag_1175_ = lean_ctor_get(v___x_1171_, 4);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v___x_1171_, 1);
lean_dec(v_unused_1205_);
v___x_1177_ = v___x_1171_;
v_isShared_1178_ = v_isSharedCheck_1204_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_diag_1175_);
lean_inc(v_postponed_1174_);
lean_inc(v_zetaDeltaFVarIds_1173_);
lean_inc(v_mctx_1172_);
lean_dec(v___x_1171_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1204_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_mctx_1172_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_zetaDeltaFVarIds_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_postponed_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_diag_1175_);
v___x_1181_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v_ref_1183_; uint8_t v_kind_1184_; lean_object* v_levelParams_1185_; lean_object* v_modifiers_1186_; lean_object* v_declName_1187_; lean_object* v_binders_1188_; lean_object* v_numSectionVars_1189_; lean_object* v_type_1190_; lean_object* v_termination_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v___x_1182_ = lean_st_ref_set(v___y_1140_, v___x_1181_);
v_ref_1183_ = lean_ctor_get(v_fst_1100_, 0);
v_kind_1184_ = lean_ctor_get_uint8(v_fst_1100_, sizeof(void*)*9);
v_levelParams_1185_ = lean_ctor_get(v_fst_1100_, 1);
v_modifiers_1186_ = lean_ctor_get(v_fst_1100_, 2);
v_declName_1187_ = lean_ctor_get(v_fst_1100_, 3);
v_binders_1188_ = lean_ctor_get(v_fst_1100_, 4);
v_numSectionVars_1189_ = lean_ctor_get(v_fst_1100_, 5);
v_type_1190_ = lean_ctor_get(v_fst_1100_, 6);
v_termination_1191_ = lean_ctor_get(v_fst_1100_, 8);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_fst_1100_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_fst_1100_, 7);
lean_dec(v_unused_1202_);
v___x_1193_ = v_fst_1100_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_termination_1191_);
lean_inc(v_type_1190_);
lean_inc(v_numSectionVars_1189_);
lean_inc(v_binders_1188_);
lean_inc(v_declName_1187_);
lean_inc(v_modifiers_1186_);
lean_inc(v_levelParams_1185_);
lean_inc(v_ref_1183_);
lean_dec(v_fst_1100_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 7, v_a_1150_);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_ref_1183_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_levelParams_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_modifiers_1186_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_declName_1187_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_binders_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_numSectionVars_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_type_1190_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_a_1150_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_termination_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*9, v_kind_1184_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1196_);
v___x_1198_ = v___x_1152_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
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
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_env_1148_);
lean_dec_ref(v_fst_1100_);
v_a_1210_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1149_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1149_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; 
lean_dec_ref(v_fst_1100_);
v_a_1218_ = lean_ctor_get(v___y_1144_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___y_1144_);
v___y_1119_ = v___y_1137_;
v___y_1120_ = v___y_1138_;
v___y_1121_ = v___y_1139_;
v___y_1122_ = v___y_1140_;
v___y_1123_ = v___y_1141_;
v___y_1124_ = v___y_1142_;
v___y_1125_ = v___y_1143_;
v_a_1126_ = v_a_1218_;
goto v___jp_1118_;
}
}
v___jp_1219_:
{
lean_object* v___x_1226_; lean_object* v_env_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_st_ref_get(v___y_1225_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1101_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v___x_1228_);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1102_, v___x_1103_, v_a_1104_);
lean_inc_ref(v_fst_1100_);
v___x_1230_ = l_Lean_Elab_WF_mkFix(v_fst_1100_, v_fixedArgs_1105_, v_fst_1106_, v_wfRel_1110_, v___x_1107_, v___x_1229_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1231_, v___y_1224_, v___y_1225_);
v___y_1137_ = v___y_1222_;
v___y_1138_ = v___y_1221_;
v___y_1139_ = v___y_1220_;
v___y_1140_ = v___y_1223_;
v___y_1141_ = v_env_1227_;
v___y_1142_ = v___y_1225_;
v___y_1143_ = v___y_1224_;
v___y_1144_ = v___x_1232_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v___y_1222_;
v___y_1138_ = v___y_1221_;
v___y_1139_ = v___y_1220_;
v___y_1140_ = v___y_1223_;
v___y_1141_ = v_env_1227_;
v___y_1142_ = v___y_1225_;
v___y_1143_ = v___y_1224_;
v___y_1144_ = v___x_1230_;
goto v___jp_1136_;
}
}
else
{
lean_object* v_a_1233_; 
lean_dec_ref(v_wfRel_1110_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_fst_1106_);
lean_dec_ref(v_fixedArgs_1105_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_fst_1100_);
v_a_1233_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1228_);
v___y_1119_ = v___y_1222_;
v___y_1120_ = v___y_1221_;
v___y_1121_ = v___y_1220_;
v___y_1122_ = v___y_1223_;
v___y_1123_ = v_env_1227_;
v___y_1124_ = v___y_1225_;
v___y_1125_ = v___y_1224_;
v_a_1126_ = v_a_1233_;
goto v___jp_1118_;
}
}
v___jp_1234_:
{
if (lean_obj_tag(v___y_1241_) == 0)
{
lean_dec_ref(v___y_1241_);
v___y_1220_ = v___y_1237_;
v___y_1221_ = v___y_1235_;
v___y_1222_ = v___y_1239_;
v___y_1223_ = v___y_1236_;
v___y_1224_ = v___y_1238_;
v___y_1225_ = v___y_1240_;
goto v___jp_1219_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_wfRel_1110_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_fst_1106_);
lean_dec_ref(v_fixedArgs_1105_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_fst_1100_);
v_a_1242_ = lean_ctor_get(v___y_1241_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___y_1241_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___y_1241_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___y_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
v___jp_1250_:
{
lean_object* v___x_1257_; 
lean_inc_ref(v_wfRel_1110_);
v___x_1257_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1110_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
if (lean_obj_tag(v_a_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_array_get_size(v_a_1104_);
v___x_1261_ = lean_nat_dec_lt(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
v___y_1220_ = v___y_1251_;
v___y_1221_ = v___y_1252_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
goto v___jp_1219_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_le(v___x_1260_, v___x_1260_);
if (v___x_1262_ == 0)
{
if (v___x_1261_ == 0)
{
v___y_1220_ = v___y_1251_;
v___y_1221_ = v___y_1252_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
goto v___jp_1219_;
}
else
{
size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_usize_of_nat(v___x_1260_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_1104_, v___x_1103_, v___x_1263_, v___x_1108_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
v___y_1235_ = v___y_1252_;
v___y_1236_ = v___y_1254_;
v___y_1237_ = v___y_1251_;
v___y_1238_ = v___y_1255_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___x_1264_;
goto v___jp_1234_;
}
}
else
{
size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_usize_of_nat(v___x_1260_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_1104_, v___x_1103_, v___x_1265_, v___x_1108_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
v___y_1235_ = v___y_1252_;
v___y_1236_ = v___y_1254_;
v___y_1237_ = v___y_1251_;
v___y_1238_ = v___y_1255_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___x_1266_;
goto v___jp_1234_;
}
}
}
else
{
lean_dec_ref(v_a_1258_);
v___y_1220_ = v___y_1251_;
v___y_1221_ = v___y_1252_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
goto v___jp_1219_;
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_wfRel_1110_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_fst_1106_);
lean_dec_ref(v_fixedArgs_1105_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_fst_1100_);
v_a_1267_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1257_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1257_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1293_ = _args[0];
lean_object* v_snd_1294_ = _args[1];
lean_object* v_sz_1295_ = _args[2];
lean_object* v___x_1296_ = _args[3];
lean_object* v_a_1297_ = _args[4];
lean_object* v_fixedArgs_1298_ = _args[5];
lean_object* v_fst_1299_ = _args[6];
lean_object* v___x_1300_ = _args[7];
lean_object* v___x_1301_ = _args[8];
lean_object* v___x_1302_ = _args[9];
lean_object* v_wfRel_1303_ = _args[10];
lean_object* v___y_1304_ = _args[11];
lean_object* v___y_1305_ = _args[12];
lean_object* v___y_1306_ = _args[13];
lean_object* v___y_1307_ = _args[14];
lean_object* v___y_1308_ = _args[15];
lean_object* v___y_1309_ = _args[16];
lean_object* v___y_1310_ = _args[17];
_start:
{
size_t v_sz_boxed_1311_; size_t v___x_47731__boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1295_);
lean_dec(v_sz_1295_);
v___x_47731__boxed_1312_ = lean_unbox_usize(v___x_1296_);
lean_dec(v___x_1296_);
v_res_1313_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1293_, v_snd_1294_, v_sz_boxed_1311_, v___x_47731__boxed_1312_, v_a_1297_, v_fixedArgs_1298_, v_fst_1299_, v___x_1300_, v___x_1301_, v___x_1302_, v_wfRel_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_snd_1294_);
return v_res_1313_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1317_, size_t v___x_1318_, lean_object* v_a_1319_, lean_object* v_fst_1320_, lean_object* v_snd_1321_, lean_object* v_fst_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_declName_1325_, lean_object* v_fst_1326_, lean_object* v_wf_1327_, lean_object* v_fixedArgs_1328_, lean_object* v_type_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_whnfForall(v_type_1329_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; uint8_t v___x_1352_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v___x_1352_ = l_Lean_Expr_isForall(v_a_1338_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_fixedArgs_1328_);
lean_dec_ref(v_wf_1327_);
lean_dec_ref(v_fst_1326_);
lean_dec(v_declName_1325_);
lean_dec(v___x_1324_);
lean_dec_ref(v_fst_1322_);
lean_dec_ref(v_snd_1321_);
lean_dec_ref(v_fst_1320_);
lean_dec_ref(v_a_1319_);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1354_ = l_Lean_MessageData_ofExpr(v_a_1338_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1355_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
v___y_1340_ = v___y_1330_;
v___y_1341_ = v___y_1331_;
v___y_1342_ = v___y_1332_;
v___y_1343_ = v___y_1333_;
v___y_1344_ = v___y_1334_;
v___y_1345_ = v___y_1335_;
goto v___jp_1339_;
}
v___jp_1339_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___f_1350_; lean_object* v___x_1351_; 
v___x_1346_ = l_Lean_Expr_bindingDomain_x21(v_a_1338_);
lean_dec(v_a_1338_);
lean_inc_ref(v_a_1319_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_1317_, v___x_1318_, v_a_1319_);
v___x_1348_ = lean_box_usize(v_sz_1317_);
v___x_1349_ = lean_box_usize(v___x_1318_);
lean_inc_ref(v___x_1347_);
lean_inc_ref(v_fst_1322_);
lean_inc_ref(v_fixedArgs_1328_);
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1350_, 0, v_fst_1320_);
lean_closure_set(v___f_1350_, 1, v_snd_1321_);
lean_closure_set(v___f_1350_, 2, v___x_1348_);
lean_closure_set(v___f_1350_, 3, v___x_1349_);
lean_closure_set(v___f_1350_, 4, v_a_1319_);
lean_closure_set(v___f_1350_, 5, v_fixedArgs_1328_);
lean_closure_set(v___f_1350_, 6, v_fst_1322_);
lean_closure_set(v___f_1350_, 7, v___x_1347_);
lean_closure_set(v___f_1350_, 8, v___x_1323_);
lean_closure_set(v___f_1350_, 9, v___x_1324_);
v___x_1351_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1347_, v_declName_1325_, v_fst_1326_, v_fixedArgs_1328_, v_fst_1322_, v___x_1346_, v_wf_1327_, v___f_1350_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1351_;
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_fixedArgs_1328_);
lean_dec_ref(v_wf_1327_);
lean_dec_ref(v_fst_1326_);
lean_dec(v_declName_1325_);
lean_dec(v___x_1324_);
lean_dec_ref(v_fst_1322_);
lean_dec_ref(v_snd_1321_);
lean_dec_ref(v_fst_1320_);
lean_dec_ref(v_a_1319_);
v_a_1365_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1337_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1337_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1373_ = _args[0];
lean_object* v___x_1374_ = _args[1];
lean_object* v_a_1375_ = _args[2];
lean_object* v_fst_1376_ = _args[3];
lean_object* v_snd_1377_ = _args[4];
lean_object* v_fst_1378_ = _args[5];
lean_object* v___x_1379_ = _args[6];
lean_object* v___x_1380_ = _args[7];
lean_object* v_declName_1381_ = _args[8];
lean_object* v_fst_1382_ = _args[9];
lean_object* v_wf_1383_ = _args[10];
lean_object* v_fixedArgs_1384_ = _args[11];
lean_object* v_type_1385_ = _args[12];
lean_object* v___y_1386_ = _args[13];
lean_object* v___y_1387_ = _args[14];
lean_object* v___y_1388_ = _args[15];
lean_object* v___y_1389_ = _args[16];
lean_object* v___y_1390_ = _args[17];
lean_object* v___y_1391_ = _args[18];
lean_object* v___y_1392_ = _args[19];
_start:
{
size_t v_sz_boxed_1393_; size_t v___x_48089__boxed_1394_; lean_object* v_res_1395_; 
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1373_);
lean_dec(v_sz_1373_);
v___x_48089__boxed_1394_ = lean_unbox_usize(v___x_1374_);
lean_dec(v___x_1374_);
v_res_1395_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1393_, v___x_48089__boxed_1394_, v_a_1375_, v_fst_1376_, v_snd_1377_, v_fst_1378_, v___x_1379_, v___x_1380_, v_declName_1381_, v_fst_1382_, v_wf_1383_, v_fixedArgs_1384_, v_type_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1396_, lean_object* v_fst_1397_, lean_object* v_fst_1398_, lean_object* v_fst_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Elab_WF_guessLex(v_a_1396_, v_fst_1397_, v_fst_1398_, v_fst_1399_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1408_, lean_object* v_fst_1409_, lean_object* v_fst_1410_, lean_object* v_fst_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1408_, v_fst_1409_, v_fst_1410_, v_fst_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1420_, uint8_t v_isExporting_1421_, lean_object* v___x_1422_, lean_object* v___y_1423_, lean_object* v___x_1424_, lean_object* v_a_x3f_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v_env_1428_; lean_object* v_nextMacroScope_1429_; lean_object* v_ngen_1430_; lean_object* v_auxDeclNGen_1431_; lean_object* v_traceState_1432_; lean_object* v_messages_1433_; lean_object* v_infoState_1434_; lean_object* v_snapshotTasks_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1460_; 
v___x_1427_ = lean_st_ref_take(v___y_1420_);
v_env_1428_ = lean_ctor_get(v___x_1427_, 0);
v_nextMacroScope_1429_ = lean_ctor_get(v___x_1427_, 1);
v_ngen_1430_ = lean_ctor_get(v___x_1427_, 2);
v_auxDeclNGen_1431_ = lean_ctor_get(v___x_1427_, 3);
v_traceState_1432_ = lean_ctor_get(v___x_1427_, 4);
v_messages_1433_ = lean_ctor_get(v___x_1427_, 6);
v_infoState_1434_ = lean_ctor_get(v___x_1427_, 7);
v_snapshotTasks_1435_ = lean_ctor_get(v___x_1427_, 8);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v___x_1427_, 5);
lean_dec(v_unused_1461_);
v___x_1437_ = v___x_1427_;
v_isShared_1438_ = v_isSharedCheck_1460_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snapshotTasks_1435_);
lean_inc(v_infoState_1434_);
lean_inc(v_messages_1433_);
lean_inc(v_traceState_1432_);
lean_inc(v_auxDeclNGen_1431_);
lean_inc(v_ngen_1430_);
lean_inc(v_nextMacroScope_1429_);
lean_inc(v_env_1428_);
lean_dec(v___x_1427_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1460_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = l_Lean_Environment_setExporting(v_env_1428_, v_isExporting_1421_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 5, v___x_1422_);
lean_ctor_set(v___x_1437_, 0, v___x_1439_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_nextMacroScope_1429_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_ngen_1430_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_auxDeclNGen_1431_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_traceState_1432_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1459_, 6, v_messages_1433_);
lean_ctor_set(v_reuseFailAlloc_1459_, 7, v_infoState_1434_);
lean_ctor_set(v_reuseFailAlloc_1459_, 8, v_snapshotTasks_1435_);
v___x_1441_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_mctx_1444_; lean_object* v_zetaDeltaFVarIds_1445_; lean_object* v_postponed_1446_; lean_object* v_diag_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1457_; 
v___x_1442_ = lean_st_ref_set(v___y_1420_, v___x_1441_);
v___x_1443_ = lean_st_ref_take(v___y_1423_);
v_mctx_1444_ = lean_ctor_get(v___x_1443_, 0);
v_zetaDeltaFVarIds_1445_ = lean_ctor_get(v___x_1443_, 2);
v_postponed_1446_ = lean_ctor_get(v___x_1443_, 3);
v_diag_1447_ = lean_ctor_get(v___x_1443_, 4);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1443_, 1);
lean_dec(v_unused_1458_);
v___x_1449_ = v___x_1443_;
v_isShared_1450_ = v_isSharedCheck_1457_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_diag_1447_);
lean_inc(v_postponed_1446_);
lean_inc(v_zetaDeltaFVarIds_1445_);
lean_inc(v_mctx_1444_);
lean_dec(v___x_1443_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1457_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v___x_1424_);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_mctx_1444_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_zetaDeltaFVarIds_1445_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_postponed_1446_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_diag_1447_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_st_ref_set(v___y_1423_, v___x_1452_);
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1462_, lean_object* v_isExporting_1463_, lean_object* v___x_1464_, lean_object* v___y_1465_, lean_object* v___x_1466_, lean_object* v_a_x3f_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_isExporting_boxed_1469_; lean_object* v_res_1470_; 
v_isExporting_boxed_1469_ = lean_unbox(v_isExporting_1463_);
v_res_1470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1462_, v_isExporting_boxed_1469_, v___x_1464_, v___y_1465_, v___x_1466_, v_a_x3f_1467_);
lean_dec(v_a_x3f_1467_);
lean_dec(v___y_1465_);
lean_dec(v___y_1462_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1471_, uint8_t v_isExporting_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; lean_object* v_env_1481_; uint8_t v_isExporting_1482_; lean_object* v___x_1483_; lean_object* v_env_1484_; lean_object* v_nextMacroScope_1485_; lean_object* v_ngen_1486_; lean_object* v_auxDeclNGen_1487_; lean_object* v_traceState_1488_; lean_object* v_messages_1489_; lean_object* v_infoState_1490_; lean_object* v_snapshotTasks_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1545_; 
v___x_1480_ = lean_st_ref_get(v___y_1478_);
v_env_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc_ref(v_env_1481_);
lean_dec(v___x_1480_);
v_isExporting_1482_ = lean_ctor_get_uint8(v_env_1481_, sizeof(void*)*8);
lean_dec_ref(v_env_1481_);
v___x_1483_ = lean_st_ref_take(v___y_1478_);
v_env_1484_ = lean_ctor_get(v___x_1483_, 0);
v_nextMacroScope_1485_ = lean_ctor_get(v___x_1483_, 1);
v_ngen_1486_ = lean_ctor_get(v___x_1483_, 2);
v_auxDeclNGen_1487_ = lean_ctor_get(v___x_1483_, 3);
v_traceState_1488_ = lean_ctor_get(v___x_1483_, 4);
v_messages_1489_ = lean_ctor_get(v___x_1483_, 6);
v_infoState_1490_ = lean_ctor_get(v___x_1483_, 7);
v_snapshotTasks_1491_ = lean_ctor_get(v___x_1483_, 8);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1483_, 5);
lean_dec(v_unused_1546_);
v___x_1493_ = v___x_1483_;
v_isShared_1494_ = v_isSharedCheck_1545_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snapshotTasks_1491_);
lean_inc(v_infoState_1490_);
lean_inc(v_messages_1489_);
lean_inc(v_traceState_1488_);
lean_inc(v_auxDeclNGen_1487_);
lean_inc(v_ngen_1486_);
lean_inc(v_nextMacroScope_1485_);
lean_inc(v_env_1484_);
lean_dec(v___x_1483_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1545_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1495_ = l_Lean_Environment_setExporting(v_env_1484_, v_isExporting_1472_);
v___x_1496_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 5, v___x_1496_);
lean_ctor_set(v___x_1493_, 0, v___x_1495_);
v___x_1498_ = v___x_1493_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_nextMacroScope_1485_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_ngen_1486_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_auxDeclNGen_1487_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_traceState_1488_);
lean_ctor_set(v_reuseFailAlloc_1544_, 5, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1544_, 6, v_messages_1489_);
lean_ctor_set(v_reuseFailAlloc_1544_, 7, v_infoState_1490_);
lean_ctor_set(v_reuseFailAlloc_1544_, 8, v_snapshotTasks_1491_);
v___x_1498_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v_mctx_1501_; lean_object* v_zetaDeltaFVarIds_1502_; lean_object* v_postponed_1503_; lean_object* v_diag_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1542_; 
v___x_1499_ = lean_st_ref_set(v___y_1478_, v___x_1498_);
v___x_1500_ = lean_st_ref_take(v___y_1476_);
v_mctx_1501_ = lean_ctor_get(v___x_1500_, 0);
v_zetaDeltaFVarIds_1502_ = lean_ctor_get(v___x_1500_, 2);
v_postponed_1503_ = lean_ctor_get(v___x_1500_, 3);
v_diag_1504_ = lean_ctor_get(v___x_1500_, 4);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v___x_1500_, 1);
lean_dec(v_unused_1543_);
v___x_1506_ = v___x_1500_;
v_isShared_1507_ = v_isSharedCheck_1542_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_diag_1504_);
lean_inc(v_postponed_1503_);
lean_inc(v_zetaDeltaFVarIds_1502_);
lean_inc(v_mctx_1501_);
lean_dec(v___x_1500_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1542_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1508_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_mctx_1501_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_zetaDeltaFVarIds_1502_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_postponed_1503_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_diag_1504_);
v___x_1510_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v_r_1512_; 
v___x_1511_ = lean_st_ref_set(v___y_1476_, v___x_1510_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1476_);
lean_inc_ref(v___y_1475_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
v_r_1512_ = lean_apply_7(v_x_1471_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, lean_box(0));
if (lean_obj_tag(v_r_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1529_; 
v_a_1513_ = lean_ctor_get(v_r_1512_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_r_1512_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1515_ = v_r_1512_;
v_isShared_1516_ = v_isSharedCheck_1529_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v_r_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1529_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
lean_inc(v_a_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 1);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v___x_1519_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1478_, v_isExporting_1482_, v___x_1496_, v___y_1476_, v___x_1508_, v___x_1518_);
lean_dec_ref(v___x_1518_);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1527_);
v___x_1521_ = v___x_1519_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v___x_1519_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_a_1513_);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1513_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1530_ = lean_ctor_get(v_r_1512_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v_r_1512_);
v___x_1531_ = lean_box(0);
v___x_1532_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1478_, v_isExporting_1482_, v___x_1496_, v___y_1476_, v___x_1508_, v___x_1531_);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1532_, 0);
lean_dec(v_unused_1540_);
v___x_1534_ = v___x_1532_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v___x_1532_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 1);
lean_ctor_set(v___x_1534_, 0, v_a_1530_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1530_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1547_, lean_object* v_isExporting_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v_isExporting_boxed_1556_; lean_object* v_res_1557_; 
v_isExporting_boxed_1556_ = lean_unbox(v_isExporting_1548_);
v_res_1557_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1547_, v_isExporting_boxed_1556_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1558_, uint8_t v_when_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
if (v_when_1559_ == 0)
{
lean_object* v___x_1567_; 
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
v___x_1567_ = lean_apply_7(v_x_1558_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, lean_box(0));
return v___x_1567_;
}
else
{
uint8_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = 0;
v___x_1569_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1558_, v___x_1568_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1570_, lean_object* v_when_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_when_boxed_1579_; lean_object* v_res_1580_; 
v_when_boxed_1579_ = lean_unbox(v_when_1571_);
v_res_1580_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1570_, v_when_boxed_1579_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_bs_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v___x_1587_; 
v___x_1587_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_bs_1583_);
return v___x_1588_;
}
else
{
lean_object* v_v_1589_; lean_object* v_ref_1590_; uint8_t v_kind_1591_; lean_object* v_levelParams_1592_; lean_object* v_modifiers_1593_; lean_object* v_declName_1594_; lean_object* v_binders_1595_; lean_object* v_numSectionVars_1596_; lean_object* v_type_1597_; lean_object* v_value_1598_; lean_object* v_termination_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1622_; 
v_v_1589_ = lean_array_uget(v_bs_1583_, v_i_1582_);
v_ref_1590_ = lean_ctor_get(v_v_1589_, 0);
v_kind_1591_ = lean_ctor_get_uint8(v_v_1589_, sizeof(void*)*9);
v_levelParams_1592_ = lean_ctor_get(v_v_1589_, 1);
v_modifiers_1593_ = lean_ctor_get(v_v_1589_, 2);
v_declName_1594_ = lean_ctor_get(v_v_1589_, 3);
v_binders_1595_ = lean_ctor_get(v_v_1589_, 4);
v_numSectionVars_1596_ = lean_ctor_get(v_v_1589_, 5);
v_type_1597_ = lean_ctor_get(v_v_1589_, 6);
v_value_1598_ = lean_ctor_get(v_v_1589_, 7);
v_termination_1599_ = lean_ctor_get(v_v_1589_, 8);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_v_1589_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1601_ = v_v_1589_;
v_isShared_1602_ = v_isSharedCheck_1622_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_termination_1599_);
lean_inc(v_value_1598_);
lean_inc(v_type_1597_);
lean_inc(v_numSectionVars_1596_);
lean_inc(v_binders_1595_);
lean_inc(v_declName_1594_);
lean_inc(v_modifiers_1593_);
lean_inc(v_levelParams_1592_);
lean_inc(v_ref_1590_);
lean_dec(v_v_1589_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1622_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Elab_WF_floatRecApp(v_value_1598_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; lean_object* v_bs_x27_1606_; lean_object* v___x_1608_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v_bs_x27_1606_ = lean_array_uset(v_bs_1583_, v_i_1582_, v___x_1605_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 7, v_a_1604_);
v___x_1608_ = v___x_1601_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_ref_1590_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_levelParams_1592_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_modifiers_1593_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_declName_1594_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_binders_1595_);
lean_ctor_set(v_reuseFailAlloc_1613_, 5, v_numSectionVars_1596_);
lean_ctor_set(v_reuseFailAlloc_1613_, 6, v_type_1597_);
lean_ctor_set(v_reuseFailAlloc_1613_, 7, v_a_1604_);
lean_ctor_set(v_reuseFailAlloc_1613_, 8, v_termination_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*9, v_kind_1591_);
v___x_1608_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
size_t v___x_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_add(v_i_1582_, v___x_1609_);
v___x_1611_ = lean_array_uset(v_bs_x27_1606_, v_i_1582_, v___x_1608_);
v_i_1582_ = v___x_1610_;
v_bs_1583_ = v___x_1611_;
goto _start;
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_del_object(v___x_1601_);
lean_dec_ref(v_termination_1599_);
lean_dec_ref(v_type_1597_);
lean_dec(v_numSectionVars_1596_);
lean_dec(v_binders_1595_);
lean_dec(v_declName_1594_);
lean_dec_ref(v_modifiers_1593_);
lean_dec(v_levelParams_1592_);
lean_dec(v_ref_1590_);
lean_dec_ref(v_bs_1583_);
v_a_1614_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1603_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1603_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* v_sz_1623_, lean_object* v_i_1624_, lean_object* v_bs_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
size_t v_sz_boxed_1629_; size_t v_i_boxed_1630_; lean_object* v_res_1631_; 
v_sz_boxed_1629_ = lean_unbox_usize(v_sz_1623_);
lean_dec(v_sz_1623_);
v_i_boxed_1630_ = lean_unbox_usize(v_i_1624_);
lean_dec(v_i_1624_);
v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_1629_, v_i_boxed_1630_, v_bs_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t v_sz_1632_, size_t v_i_1633_, lean_object* v_bs_1634_){
_start:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_usize_dec_lt(v_i_1633_, v_sz_1632_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_bs_1634_);
return v___x_1636_;
}
else
{
lean_object* v_v_1637_; 
v_v_1637_ = lean_array_uget_borrowed(v_bs_1634_, v_i_1633_);
if (lean_obj_tag(v_v_1637_) == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref(v_bs_1634_);
v___x_1638_ = lean_box(0);
return v___x_1638_;
}
else
{
lean_object* v_val_1639_; lean_object* v___x_1640_; lean_object* v_bs_x27_1641_; size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_val_1639_ = lean_ctor_get(v_v_1637_, 0);
lean_inc(v_val_1639_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v_bs_x27_1641_ = lean_array_uset(v_bs_1634_, v_i_1633_, v___x_1640_);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_add(v_i_1633_, v___x_1642_);
v___x_1644_ = lean_array_uset(v_bs_x27_1641_, v_i_1633_, v_val_1639_);
v_i_1633_ = v___x_1643_;
v_bs_1634_ = v___x_1644_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_sz_1646_, lean_object* v_i_1647_, lean_object* v_bs_1648_){
_start:
{
size_t v_sz_boxed_1649_; size_t v_i_boxed_1650_; lean_object* v_res_1651_; 
v_sz_boxed_1649_ = lean_unbox_usize(v_sz_1646_);
lean_dec(v_sz_1646_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_boxed_1649_, v_i_boxed_1650_, v_bs_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1652_, size_t v_i_1653_, lean_object* v_bs_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_bs_1654_);
return v___x_1661_;
}
else
{
uint8_t v___x_1662_; lean_object* v_v_1663_; lean_object* v___x_1664_; 
v___x_1662_ = 0;
v_v_1663_ = lean_array_uget_borrowed(v_bs_1654_, v_i_1653_);
lean_inc(v_v_1663_);
v___x_1664_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1663_, v___x_1662_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v_bs_x27_1667_; size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = lean_unsigned_to_nat(0u);
v_bs_x27_1667_ = lean_array_uset(v_bs_1654_, v_i_1653_, v___x_1666_);
v___x_1668_ = ((size_t)1ULL);
v___x_1669_ = lean_usize_add(v_i_1653_, v___x_1668_);
v___x_1670_ = lean_array_uset(v_bs_x27_1667_, v_i_1653_, v_a_1665_);
v_i_1653_ = v___x_1669_;
v_bs_1654_ = v___x_1670_;
goto _start;
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v_bs_1654_);
v_a_1672_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1664_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1664_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1680_, lean_object* v_i_1681_, lean_object* v_bs_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
size_t v_sz_boxed_1688_; size_t v_i_boxed_1689_; lean_object* v_res_1690_; 
v_sz_boxed_1688_ = lean_unbox_usize(v_sz_1680_);
lean_dec(v_sz_1680_);
v_i_boxed_1689_ = lean_unbox_usize(v_i_1681_);
lean_dec(v_i_1681_);
v_res_1690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1688_, v_i_boxed_1689_, v_bs_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_env_1691_, lean_object* v_x_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; lean_object* v_env_1701_; lean_object* v_a_1703_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1700_ = lean_st_ref_get(v___y_1698_);
v_env_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc_ref(v_env_1701_);
lean_dec(v___x_1700_);
v___x_1713_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1691_, v___y_1696_, v___y_1698_);
lean_dec_ref(v___x_1713_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc_ref(v___y_1695_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
v___x_1714_ = lean_apply_7(v_x_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, lean_box(0));
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1701_, v___y_1696_, v___y_1698_);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1716_, 0);
lean_dec(v_unused_1724_);
v___x_1718_ = v___x_1716_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_dec(v___x_1716_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v_a_1715_);
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1715_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1725_; 
v_a_1725_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1714_);
v_a_1703_ = v_a_1725_;
goto v___jp_1702_;
}
v___jp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v___x_1704_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1701_, v___y_1696_, v___y_1698_);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v___x_1704_, 0);
lean_dec(v_unused_1712_);
v___x_1706_ = v___x_1704_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_dec(v___x_1704_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
lean_ctor_set(v___x_1706_, 0, v_a_1703_);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1703_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_env_1726_, lean_object* v_x_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_1726_, v_x_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1736_, lean_object* v_as_1737_, size_t v_sz_1738_, size_t v_i_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_a_1747_; uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_lt(v_i_1739_, v_sz_1738_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v___x_1736_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_b_1740_);
return v___x_1752_;
}
else
{
lean_object* v_a_1753_; uint8_t v_kind_1754_; lean_object* v_declName_1755_; lean_object* v_type_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_a_1753_ = lean_array_uget_borrowed(v_as_1737_, v_i_1739_);
v_kind_1754_ = lean_ctor_get_uint8(v_a_1753_, sizeof(void*)*9);
v_declName_1755_ = lean_ctor_get(v_a_1753_, 3);
v_type_1756_ = lean_ctor_get(v_a_1753_, 6);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_name_eq(v_declName_1755_, v___x_1736_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1754_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_inc_ref(v_type_1756_);
v___x_1760_ = l_Lean_Meta_isProp(v_type_1756_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; uint8_t v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = lean_unbox(v_a_1761_);
lean_dec(v_a_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
lean_inc(v___x_1736_);
lean_inc(v_a_1753_);
v___x_1763_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1753_, v___x_1736_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_dec_ref(v___x_1763_);
v_a_1747_ = v___x_1757_;
goto v___jp_1746_;
}
else
{
lean_dec(v___x_1736_);
return v___x_1763_;
}
}
else
{
v_a_1747_ = v___x_1757_;
goto v___jp_1746_;
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v___x_1736_);
v_a_1764_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1760_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1760_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
v_a_1747_ = v___x_1757_;
goto v___jp_1746_;
}
}
else
{
v_a_1747_ = v___x_1757_;
goto v___jp_1746_;
}
}
v___jp_1746_:
{
size_t v___x_1748_; size_t v___x_1749_; 
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_i_1739_, v___x_1748_);
v_i_1739_ = v___x_1749_;
v_b_1740_ = v_a_1747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1772_, lean_object* v_as_1773_, lean_object* v_sz_1774_, lean_object* v_i_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
size_t v_sz_boxed_1782_; size_t v_i_boxed_1783_; lean_object* v_res_1784_; 
v_sz_boxed_1782_ = lean_unbox_usize(v_sz_1774_);
lean_dec(v_sz_1774_);
v_i_boxed_1783_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1772_, v_as_1773_, v_sz_boxed_1782_, v_i_boxed_1783_, v_b_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_as_1773_);
return v_res_1784_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1805_, lean_object* v_preDefs_1806_, lean_object* v_termMeasure_x3fs_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v_sz_1815_ = lean_array_size(v_preDefs_1806_);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_1815_, v___x_1816_, v_preDefs_1806_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; lean_object* v_env_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; size_t v_sz_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc_n(v_a_1818_, 2);
lean_dec_ref(v___x_1817_);
v___x_1819_ = lean_st_ref_get(v_a_1813_);
v_env_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc_ref(v_env_1820_);
lean_dec(v___x_1819_);
v___x_1821_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1822_ = lean_box(0);
v_sz_1836_ = lean_array_size(v_a_1818_);
v___x_1837_ = lean_box_usize(v_sz_1836_);
v___x_1838_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1839_, 0, v_a_1818_);
lean_closure_set(v___f_1839_, 1, v___x_1837_);
lean_closure_set(v___f_1839_, 2, v___x_1838_);
lean_closure_set(v___f_1839_, 3, v___x_1822_);
lean_closure_set(v___f_1839_, 4, v___x_1821_);
v___x_1840_ = l_Lean_Environment_unlockAsync(v_env_1820_);
v___x_1841_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1840_, v___f_1839_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v_snd_1843_; lean_object* v_fst_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_2031_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v_snd_1843_ = lean_ctor_get(v_a_1842_, 1);
v_fst_1844_ = lean_ctor_get(v_a_1842_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1846_ = v_a_1842_;
v_isShared_1847_ = v_isSharedCheck_2031_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1843_);
lean_inc(v_fst_1844_);
lean_dec(v_a_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_2031_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_fst_1848_; lean_object* v_snd_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_2030_; 
v_fst_1848_ = lean_ctor_get(v_snd_1843_, 0);
v_snd_1849_ = lean_ctor_get(v_snd_1843_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_snd_1843_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_1851_ = v_snd_1843_;
v_isShared_1852_ = v_isSharedCheck_2030_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_snd_1849_);
lean_inc(v_fst_1848_);
lean_dec(v_snd_1843_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_2030_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___x_1912_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v_wf_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___x_1958_; lean_object* v_a_1959_; lean_object* v___f_1960_; size_t v_sz_1961_; lean_object* v_termMeasures_x3f_1962_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; uint8_t v___x_2023_; 
v___x_1912_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_1958_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1912_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref(v___x_1958_);
lean_inc(v_snd_1849_);
v___f_1960_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1960_, 0, v_snd_1849_);
v_sz_1961_ = lean_array_size(v_termMeasure_x3fs_1807_);
v_termMeasures_x3f_1962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_1961_, v___x_1816_, v_termMeasure_x3fs_1807_);
v___x_2023_ = lean_unbox(v_a_1959_);
lean_dec(v_a_1959_);
if (v___x_2023_ == 0)
{
v___y_1986_ = v_a_1808_;
v___y_1987_ = v_a_1809_;
v___y_1988_ = v_a_1810_;
v___y_1989_ = v_a_1811_;
v___y_1990_ = v_a_1812_;
v___y_1991_ = v_a_1813_;
goto v___jp_1985_;
}
else
{
lean_object* v_value_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_value_2024_ = lean_ctor_get(v_snd_1849_, 7);
v___x_2025_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2024_);
v___x_2026_ = l_Lean_MessageData_ofExpr(v_value_2024_);
v___x_2027_ = l_Lean_indentD(v___x_2026_);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2025_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1912_, v___x_2028_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref(v___x_2029_);
v___y_1986_ = v_a_1808_;
v___y_1987_ = v_a_1809_;
v___y_1988_ = v_a_1810_;
v___y_1989_ = v_a_1811_;
v___y_1990_ = v_a_1812_;
v___y_1991_ = v_a_1813_;
goto v___jp_1985_;
}
else
{
lean_dec(v_termMeasures_x3f_1962_);
lean_dec_ref(v___f_1960_);
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_del_object(v___x_1846_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
return v___x_2029_;
}
}
v___jp_1853_:
{
lean_object* v___x_1863_; 
lean_inc_ref(v___y_1854_);
lean_inc(v_a_1818_);
lean_inc(v_fst_1848_);
lean_inc(v_fst_1844_);
v___x_1863_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1844_, v_fst_1848_, v_a_1818_, v___y_1854_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
lean_inc_ref(v___y_1854_);
lean_inc(v_a_1818_);
lean_inc_ref(v_docCtx_1805_);
v___x_1865_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1805_, v_a_1818_, v_a_1864_, v___y_1854_, v___y_1855_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v_a_1864_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v___x_1866_; 
lean_dec_ref(v___x_1865_);
lean_inc(v_a_1818_);
v___x_1866_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1805_, v_a_1818_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v___x_1867_; 
lean_dec_ref(v___x_1866_);
v___x_1867_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1849_, v___y_1855_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1836_, v___x_1816_, v_a_1818_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_declName_1871_; lean_object* v___x_1872_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc_n(v_a_1870_, 2);
lean_dec_ref(v___x_1869_);
v_declName_1871_ = lean_ctor_get(v___y_1854_, 3);
lean_inc_n(v_declName_1871_, 2);
lean_dec_ref(v___y_1854_);
v___x_1872_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1870_, v_declName_1871_, v_fst_1844_, v_fst_1848_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_declName_1873_; lean_object* v_type_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v___x_1872_);
v_declName_1873_ = lean_ctor_get(v_a_1868_, 3);
v_type_1874_ = lean_ctor_get(v_a_1868_, 6);
lean_inc(v_declName_1873_);
v___x_1875_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1873_, v___y_1862_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref(v___x_1875_);
lean_inc_ref(v_type_1874_);
v___x_1876_ = l_Lean_Meta_isProp(v_type_1874_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; uint8_t v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = lean_unbox(v_a_1877_);
lean_dec(v_a_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_inc(v_declName_1871_);
v___x_1879_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1868_, v_declName_1871_, v___y_1856_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_dec_ref(v___x_1879_);
v___y_1824_ = v_declName_1871_;
v___y_1825_ = v_a_1870_;
v___y_1826_ = v___y_1857_;
v___y_1827_ = v___y_1858_;
v___y_1828_ = v___y_1859_;
v___y_1829_ = v___y_1860_;
v___y_1830_ = v___y_1861_;
v___y_1831_ = v___y_1862_;
goto v___jp_1823_;
}
else
{
lean_dec(v_declName_1871_);
lean_dec(v_a_1870_);
return v___x_1879_;
}
}
else
{
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1856_);
v___y_1824_ = v_declName_1871_;
v___y_1825_ = v_a_1870_;
v___y_1826_ = v___y_1857_;
v___y_1827_ = v___y_1858_;
v___y_1828_ = v___y_1859_;
v___y_1829_ = v___y_1860_;
v___y_1830_ = v___y_1861_;
v___y_1831_ = v___y_1862_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_declName_1871_);
lean_dec(v_a_1870_);
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1856_);
v_a_1880_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1876_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_dec(v_declName_1871_);
lean_dec(v_a_1870_);
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1856_);
return v___x_1875_;
}
}
else
{
lean_dec(v_declName_1871_);
lean_dec(v_a_1870_);
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1856_);
return v___x_1872_;
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1854_);
lean_dec(v_fst_1848_);
lean_dec(v_fst_1844_);
v_a_1888_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1869_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1869_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1854_);
lean_dec(v_fst_1848_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
v_a_1896_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1867_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1867_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1854_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
return v___x_1866_;
}
}
else
{
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1854_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
return v___x_1865_;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1854_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
v_a_1904_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1863_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1863_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
v___jp_1913_:
{
lean_object* v_declName_1923_; lean_object* v_type_1924_; lean_object* v_numFixed_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; 
v_declName_1923_ = lean_ctor_get(v_snd_1849_, 3);
v_type_1924_ = lean_ctor_get(v_snd_1849_, 6);
v_numFixed_1925_ = lean_ctor_get(v_fst_1844_, 0);
v___x_1926_ = lean_box_usize(v_sz_1836_);
v___x_1927_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1844_);
lean_inc(v_declName_1923_);
lean_inc(v_fst_1848_);
lean_inc(v_snd_1849_);
lean_inc(v_a_1818_);
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1928_, 0, v___x_1926_);
lean_closure_set(v___f_1928_, 1, v___x_1927_);
lean_closure_set(v___f_1928_, 2, v_a_1818_);
lean_closure_set(v___f_1928_, 3, v___y_1914_);
lean_closure_set(v___f_1928_, 4, v_snd_1849_);
lean_closure_set(v___f_1928_, 5, v_fst_1848_);
lean_closure_set(v___f_1928_, 6, v___x_1822_);
lean_closure_set(v___f_1928_, 7, v___x_1912_);
lean_closure_set(v___f_1928_, 8, v_declName_1923_);
lean_closure_set(v___f_1928_, 9, v_fst_1844_);
lean_closure_set(v___f_1928_, 10, v_wf_1916_);
lean_inc(v_numFixed_1925_);
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_numFixed_1925_);
v___x_1930_ = 0;
lean_inc_ref(v_type_1924_);
v___x_1931_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1924_, v___x_1929_, v___f_1928_, v___x_1930_, v___x_1930_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; uint8_t v___x_1935_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1912_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = lean_unbox(v_a_1934_);
lean_dec(v_a_1934_);
if (v___x_1935_ == 0)
{
lean_del_object(v___x_1851_);
lean_del_object(v___x_1846_);
v___y_1854_ = v_a_1932_;
v___y_1855_ = v___x_1930_;
v___y_1856_ = v___y_1915_;
v___y_1857_ = v___y_1917_;
v___y_1858_ = v___y_1918_;
v___y_1859_ = v___y_1919_;
v___y_1860_ = v___y_1920_;
v___y_1861_ = v___y_1921_;
v___y_1862_ = v___y_1922_;
goto v___jp_1853_;
}
else
{
lean_object* v_declName_1936_; lean_object* v_value_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v_declName_1936_ = lean_ctor_get(v_a_1932_, 3);
v_value_1937_ = lean_ctor_get(v_a_1932_, 7);
v___x_1938_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1936_);
v___x_1939_ = l_Lean_MessageData_ofName(v_declName_1936_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 7);
lean_ctor_set(v___x_1851_, 1, v___x_1939_);
lean_ctor_set(v___x_1851_, 0, v___x_1938_);
v___x_1941_ = v___x_1851_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 7);
lean_ctor_set(v___x_1846_, 1, v___x_1942_);
lean_ctor_set(v___x_1846_, 0, v___x_1941_);
v___x_1944_ = v___x_1846_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_inc_ref(v_value_1937_);
v___x_1945_ = l_Lean_MessageData_ofExpr(v_value_1937_);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1912_, v___x_1946_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_dec_ref(v___x_1947_);
v___y_1854_ = v_a_1932_;
v___y_1855_ = v___x_1930_;
v___y_1856_ = v___y_1915_;
v___y_1857_ = v___y_1917_;
v___y_1858_ = v___y_1918_;
v___y_1859_ = v___y_1919_;
v___y_1860_ = v___y_1920_;
v___y_1861_ = v___y_1921_;
v___y_1862_ = v___y_1922_;
goto v___jp_1853_;
}
else
{
lean_dec(v_a_1932_);
lean_dec_ref(v___y_1915_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
return v___x_1947_;
}
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v___y_1915_);
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_del_object(v___x_1846_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
v_a_1950_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1931_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1931_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
v___jp_1963_:
{
if (lean_obj_tag(v_termMeasures_x3f_1962_) == 1)
{
lean_object* v_val_1973_; 
lean_dec_ref(v___y_1965_);
v_val_1973_ = lean_ctor_get(v_termMeasures_x3f_1962_, 0);
lean_inc(v_val_1973_);
lean_dec_ref(v_termMeasures_x3f_1962_);
v___y_1914_ = v___y_1964_;
v___y_1915_ = v___y_1966_;
v_wf_1916_ = v_val_1973_;
v___y_1917_ = v___y_1967_;
v___y_1918_ = v___y_1968_;
v___y_1919_ = v___y_1969_;
v___y_1920_ = v___y_1970_;
v___y_1921_ = v___y_1971_;
v___y_1922_ = v___y_1972_;
goto v___jp_1913_;
}
else
{
uint8_t v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_termMeasures_x3f_1962_);
v___x_1974_ = 1;
v___x_1975_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1965_, v___x_1974_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v___y_1914_ = v___y_1964_;
v___y_1915_ = v___y_1966_;
v_wf_1916_ = v_a_1976_;
v___y_1917_ = v___y_1967_;
v___y_1918_ = v___y_1968_;
v___y_1919_ = v___y_1969_;
v___y_1920_ = v___y_1970_;
v___y_1921_ = v___y_1971_;
v___y_1922_ = v___y_1972_;
goto v___jp_1913_;
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v___y_1966_);
lean_dec_ref(v___y_1964_);
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_del_object(v___x_1846_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
v_a_1977_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1975_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
v___jp_1985_:
{
lean_object* v___x_1992_; lean_object* v_env_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1992_ = lean_st_ref_get(v___y_1991_);
v_env_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_ref(v_env_1993_);
lean_dec(v___x_1992_);
v___x_1994_ = l_Lean_Environment_unlockAsync(v_env_1993_);
v___x_1995_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1994_, v___f_1960_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v_fst_1997_; lean_object* v_snd_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2014_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1995_);
v_fst_1997_ = lean_ctor_get(v_a_1996_, 0);
v_snd_1998_ = lean_ctor_get(v_a_1996_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1996_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2000_ = v_a_1996_;
v_isShared_2001_ = v_isSharedCheck_2014_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_snd_1998_);
lean_inc(v_fst_1997_);
lean_dec(v_a_1996_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2014_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v_a_2003_; lean_object* v___f_2004_; uint8_t v___x_2005_; 
v___x_2002_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1912_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
lean_inc(v_fst_1848_);
lean_inc(v_fst_1844_);
lean_inc(v_fst_1997_);
lean_inc(v_a_1818_);
v___f_2004_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2004_, 0, v_a_1818_);
lean_closure_set(v___f_2004_, 1, v_fst_1997_);
lean_closure_set(v___f_2004_, 2, v_fst_1844_);
lean_closure_set(v___f_2004_, 3, v_fst_1848_);
v___x_2005_ = lean_unbox(v_a_2003_);
lean_dec(v_a_2003_);
if (v___x_2005_ == 0)
{
lean_del_object(v___x_2000_);
v___y_1964_ = v_fst_1997_;
v___y_1965_ = v___f_2004_;
v___y_1966_ = v_snd_1998_;
v___y_1967_ = v___y_1986_;
v___y_1968_ = v___y_1987_;
v___y_1969_ = v___y_1988_;
v___y_1970_ = v___y_1989_;
v___y_1971_ = v___y_1990_;
v___y_1972_ = v___y_1991_;
goto v___jp_1963_;
}
else
{
lean_object* v_value_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v_value_2006_ = lean_ctor_get(v_snd_1849_, 7);
v___x_2007_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2006_);
v___x_2008_ = l_Lean_MessageData_ofExpr(v_value_2006_);
v___x_2009_ = l_Lean_indentD(v___x_2008_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 7);
lean_ctor_set(v___x_2000_, 1, v___x_2009_);
lean_ctor_set(v___x_2000_, 0, v___x_2007_);
v___x_2011_ = v___x_2000_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1912_, v___x_2011_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref(v___x_2012_);
v___y_1964_ = v_fst_1997_;
v___y_1965_ = v___f_2004_;
v___y_1966_ = v_snd_1998_;
v___y_1967_ = v___y_1986_;
v___y_1968_ = v___y_1987_;
v___y_1969_ = v___y_1988_;
v___y_1970_ = v___y_1989_;
v___y_1971_ = v___y_1990_;
v___y_1972_ = v___y_1991_;
goto v___jp_1963_;
}
else
{
lean_dec_ref(v___f_2004_);
lean_dec(v_snd_1998_);
lean_dec(v_fst_1997_);
lean_dec(v_termMeasures_x3f_1962_);
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_del_object(v___x_1846_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
return v___x_2012_;
}
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_termMeasures_x3f_1962_);
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_del_object(v___x_1846_);
lean_dec(v_fst_1844_);
lean_dec(v_a_1818_);
lean_dec_ref(v_docCtx_1805_);
v_a_2015_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1995_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1995_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_termMeasure_x3fs_1807_);
lean_dec_ref(v_docCtx_1805_);
v_a_2032_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1841_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1841_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
v___jp_1823_:
{
size_t v_sz_1832_; lean_object* v___x_1833_; 
v_sz_1832_ = lean_array_size(v___y_1825_);
lean_inc(v___y_1824_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1824_, v___y_1825_, v_sz_1832_, v___x_1816_, v___x_1822_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref(v___x_1833_);
v___x_1834_ = l_Lean_enableRealizationsForConst(v___y_1824_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v___x_1834_);
v___x_1835_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1835_;
}
else
{
lean_dec_ref(v___y_1825_);
return v___x_1834_;
}
}
else
{
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_termMeasure_x3fs_1807_);
lean_dec_ref(v_docCtx_1805_);
v_a_2040_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1817_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1817_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2048_, lean_object* v_preDefs_2049_, lean_object* v_termMeasure_x3fs_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Elab_wfRecursion(v_docCtx_2048_, v_preDefs_2049_, v_termMeasure_x3fs_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2059_, lean_object* v_msg_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2069_, v_msg_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_bs_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_2079_, v_i_2080_, v_bs_2081_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_2090_, lean_object* v_i_2091_, lean_object* v_bs_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
size_t v_sz_boxed_2100_; size_t v_i_boxed_2101_; lean_object* v_res_2102_; 
v_sz_boxed_2100_ = lean_unbox_usize(v_sz_2090_);
lean_dec(v_sz_2090_);
v_i_boxed_2101_ = lean_unbox_usize(v_i_2091_);
lean_dec(v_i_2091_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_2100_, v_i_boxed_2101_, v_bs_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object* v_as_2103_, size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_b_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2103_, v_sz_2104_, v_i_2105_, v_b_2106_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_as_2115_, lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_b_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_2115_, v_sz_boxed_2126_, v_i_boxed_2127_, v_b_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_as_2115_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_a_2129_, lean_object* v_as_2130_, lean_object* v_i_2131_, lean_object* v_j_2132_, lean_object* v_inv_2133_, lean_object* v_bs_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_2129_, v_as_2130_, v_i_2131_, v_j_2132_, v_bs_2134_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_a_2143_, lean_object* v_as_2144_, lean_object* v_i_2145_, lean_object* v_j_2146_, lean_object* v_inv_2147_, lean_object* v_bs_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(v_a_2143_, v_as_2144_, v_i_2145_, v_j_2146_, v_inv_2147_, v_bs_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_as_2144_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object* v_a_2157_, lean_object* v___x_2158_, size_t v_sz_2159_, size_t v_i_2160_, lean_object* v_bs_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2157_, v___x_2158_, v_sz_2159_, v_i_2160_, v_bs_2161_, v___y_2166_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_a_2170_, lean_object* v___x_2171_, lean_object* v_sz_2172_, lean_object* v_i_2173_, lean_object* v_bs_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
size_t v_sz_boxed_2182_; size_t v_i_boxed_2183_; lean_object* v_res_2184_; 
v_sz_boxed_2182_ = lean_unbox_usize(v_sz_2172_);
lean_dec(v_sz_2172_);
v_i_boxed_2183_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_res_2184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_2170_, v___x_2171_, v_sz_boxed_2182_, v_i_boxed_2183_, v_bs_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_00_u03b1_2185_, lean_object* v_env_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_2186_, v_x_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_env_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(v_00_u03b1_2196_, v_env_2197_, v_x_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2207_, lean_object* v_msg_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2207_, v_msg_2208_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2217_, lean_object* v_msg_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2217_, v_msg_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2227_, size_t v_i_2228_, lean_object* v_bs_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2227_, v_i_2228_, v_bs_2229_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_bs_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
size_t v_sz_boxed_2248_; size_t v_i_boxed_2249_; lean_object* v_res_2250_; 
v_sz_boxed_2248_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2249_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2248_, v_i_boxed_2249_, v_bs_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2251_, lean_object* v_as_2252_, size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_b_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2251_, v_as_2252_, v_sz_2253_, v_i_2254_, v_b_2255_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2264_, lean_object* v_as_2265_, lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_b_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
size_t v_sz_boxed_2276_; size_t v_i_boxed_2277_; lean_object* v_res_2278_; 
v_sz_boxed_2276_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2277_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2264_, v_as_2265_, v_sz_boxed_2276_, v_i_boxed_2277_, v_b_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_as_2265_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2279_, lean_object* v_x_2280_, uint8_t v_isExporting_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2280_, v_isExporting_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2290_, lean_object* v_x_2291_, lean_object* v_isExporting_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v_isExporting_boxed_2300_; lean_object* v_res_2301_; 
v_isExporting_boxed_2300_ = lean_unbox(v_isExporting_2292_);
v_res_2301_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2290_, v_x_2291_, v_isExporting_boxed_2300_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2302_, lean_object* v_x_2303_, uint8_t v_when_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2303_, v_when_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2313_, lean_object* v_x_2314_, lean_object* v_when_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
uint8_t v_when_boxed_2323_; lean_object* v_res_2324_; 
v_when_boxed_2323_ = lean_unbox(v_when_2315_);
v_res_2324_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2313_, v_x_2314_, v_when_boxed_2323_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2325_, lean_object* v_macroStack_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2325_, v_macroStack_2326_, v___y_2331_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2335_, lean_object* v_macroStack_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2335_, v_macroStack_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2345_, lean_object* v_msgData_2346_, uint8_t v_severity_2347_, uint8_t v_isSilent_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2345_, v_msgData_2346_, v_severity_2347_, v_isSilent_2348_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2357_, lean_object* v_msgData_2358_, lean_object* v_severity_2359_, lean_object* v_isSilent_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
uint8_t v_severity_boxed_2368_; uint8_t v_isSilent_boxed_2369_; lean_object* v_res_2370_; 
v_severity_boxed_2368_ = lean_unbox(v_severity_2359_);
v_isSilent_boxed_2369_ = lean_unbox(v_isSilent_2360_);
v_res_2370_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2357_, v_msgData_2358_, v_severity_boxed_2368_, v_isSilent_boxed_2369_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_ref_2357_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2442_ = 0;
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2444_ = l_Lean_registerTraceClass(v___x_2441_, v___x_2442_, v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2446_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
}
#ifdef __cplusplus
}
#endif
