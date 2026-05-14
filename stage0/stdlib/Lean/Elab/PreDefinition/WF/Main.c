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
lean_object* v___x_12_; lean_object* v_nextMacroScope_13_; lean_object* v_ngen_14_; lean_object* v_auxDeclNGen_15_; lean_object* v_traceState_16_; lean_object* v_messages_17_; lean_object* v_infoState_18_; lean_object* v_snapshotTasks_19_; lean_object* v_newDecls_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_46_; 
v___x_12_ = lean_st_ref_take(v___y_10_);
v_nextMacroScope_13_ = lean_ctor_get(v___x_12_, 1);
v_ngen_14_ = lean_ctor_get(v___x_12_, 2);
v_auxDeclNGen_15_ = lean_ctor_get(v___x_12_, 3);
v_traceState_16_ = lean_ctor_get(v___x_12_, 4);
v_messages_17_ = lean_ctor_get(v___x_12_, 6);
v_infoState_18_ = lean_ctor_get(v___x_12_, 7);
v_snapshotTasks_19_ = lean_ctor_get(v___x_12_, 8);
v_newDecls_20_ = lean_ctor_get(v___x_12_, 9);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; lean_object* v_unused_48_; 
v_unused_47_ = lean_ctor_get(v___x_12_, 5);
lean_dec(v_unused_47_);
v_unused_48_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_48_);
v___x_22_ = v___x_12_;
v_isShared_23_ = v_isSharedCheck_46_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_newDecls_20_);
lean_inc(v_snapshotTasks_19_);
lean_inc(v_infoState_18_);
lean_inc(v_messages_17_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_15_);
lean_inc(v_ngen_14_);
lean_inc(v_nextMacroScope_13_);
lean_dec(v___x_12_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_46_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 5, v___x_24_);
lean_ctor_set(v___x_22_, 0, v_env_8_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_env_8_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_nextMacroScope_13_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v_ngen_14_);
lean_ctor_set(v_reuseFailAlloc_45_, 3, v_auxDeclNGen_15_);
lean_ctor_set(v_reuseFailAlloc_45_, 4, v_traceState_16_);
lean_ctor_set(v_reuseFailAlloc_45_, 5, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_45_, 6, v_messages_17_);
lean_ctor_set(v_reuseFailAlloc_45_, 7, v_infoState_18_);
lean_ctor_set(v_reuseFailAlloc_45_, 8, v_snapshotTasks_19_);
lean_ctor_set(v_reuseFailAlloc_45_, 9, v_newDecls_20_);
v___x_26_ = v_reuseFailAlloc_45_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v_mctx_29_; lean_object* v_zetaDeltaFVarIds_30_; lean_object* v_postponed_31_; lean_object* v_diag_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_43_; 
v___x_27_ = lean_st_ref_set(v___y_10_, v___x_26_);
v___x_28_ = lean_st_ref_take(v___y_9_);
v_mctx_29_ = lean_ctor_get(v___x_28_, 0);
v_zetaDeltaFVarIds_30_ = lean_ctor_get(v___x_28_, 2);
v_postponed_31_ = lean_ctor_get(v___x_28_, 3);
v_diag_32_ = lean_ctor_get(v___x_28_, 4);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_28_, 1);
lean_dec(v_unused_44_);
v___x_34_ = v___x_28_;
v_isShared_35_ = v_isSharedCheck_43_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_diag_32_);
lean_inc(v_postponed_31_);
lean_inc(v_zetaDeltaFVarIds_30_);
lean_inc(v_mctx_29_);
lean_dec(v___x_28_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_43_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_mctx_29_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v_zetaDeltaFVarIds_30_);
lean_ctor_set(v_reuseFailAlloc_42_, 3, v_postponed_31_);
lean_ctor_set(v_reuseFailAlloc_42_, 4, v_diag_32_);
v___x_38_ = v_reuseFailAlloc_42_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_st_ref_set(v___y_9_, v___x_38_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec(v___y_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_54_, v___y_58_, v___y_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object* v_k_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v_b_75_, lean_object* v_c_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; 
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
lean_inc(v___y_74_);
lean_inc_ref(v___y_73_);
v___x_82_ = lean_apply_9(v_k_72_, v_b_75_, v_c_76_, v___y_73_, v___y_74_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object* v_k_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v_b_86_, lean_object* v_c_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_83_, v___y_84_, v___y_85_, v_b_86_, v_c_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_type_94_, lean_object* v_maxFVars_x3f_95_, lean_object* v_k_96_, uint8_t v_cleanupAnnotations_97_, uint8_t v_whnfType_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; 
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_106_, 0, v_k_96_);
lean_closure_set(v___f_106_, 1, v___y_99_);
lean_closure_set(v___f_106_, 2, v___y_100_);
v___x_107_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_94_, v_maxFVars_x3f_95_, v___f_106_, v_cleanupAnnotations_97_, v_whnfType_98_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_107_) == 0)
{
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_type_116_, lean_object* v_maxFVars_x3f_117_, lean_object* v_k_118_, lean_object* v_cleanupAnnotations_119_, lean_object* v_whnfType_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_128_; uint8_t v_whnfType_boxed_129_; lean_object* v_res_130_; 
v_cleanupAnnotations_boxed_128_ = lean_unbox(v_cleanupAnnotations_119_);
v_whnfType_boxed_129_ = lean_unbox(v_whnfType_120_);
v_res_130_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_116_, v_maxFVars_x3f_117_, v_k_118_, v_cleanupAnnotations_boxed_128_, v_whnfType_boxed_129_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_00_u03b1_131_, lean_object* v_type_132_, lean_object* v_maxFVars_x3f_133_, lean_object* v_k_134_, uint8_t v_cleanupAnnotations_135_, uint8_t v_whnfType_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_132_, v_maxFVars_x3f_133_, v_k_134_, v_cleanupAnnotations_135_, v_whnfType_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_00_u03b1_145_, lean_object* v_type_146_, lean_object* v_maxFVars_x3f_147_, lean_object* v_k_148_, lean_object* v_cleanupAnnotations_149_, lean_object* v_whnfType_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_158_; uint8_t v_whnfType_boxed_159_; lean_object* v_res_160_; 
v_cleanupAnnotations_boxed_158_ = lean_unbox(v_cleanupAnnotations_149_);
v_whnfType_boxed_159_ = lean_unbox(v_whnfType_150_);
v_res_160_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(v_00_u03b1_145_, v_type_146_, v_maxFVars_x3f_147_, v_k_148_, v_cleanupAnnotations_boxed_158_, v_whnfType_boxed_159_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_160_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(1);
v___x_162_ = l_Lean_MessageData_ofFormat(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2));
v___x_167_ = l_Lean_MessageData_ofFormat(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
return v_x_168_;
}
else
{
lean_object* v_head_170_; lean_object* v_tail_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_193_; 
v_head_170_ = lean_ctor_get(v_x_169_, 0);
v_tail_171_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_193_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_193_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_tail_171_);
lean_inc(v_head_170_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_193_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_before_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_191_; 
v_before_175_ = lean_ctor_get(v_head_170_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_head_170_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_head_170_, 1);
lean_dec(v_unused_192_);
v___x_177_ = v_head_170_;
v_isShared_178_ = v_isSharedCheck_191_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_before_175_);
lean_dec(v_head_170_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_191_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 7);
lean_ctor_set(v___x_177_, 1, v___x_179_);
lean_ctor_set(v___x_177_, 0, v_x_168_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_x_168_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_190_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 7);
lean_ctor_set(v___x_173_, 1, v___x_182_);
lean_ctor_set(v___x_173_, 0, v___x_181_);
v___x_184_ = v___x_173_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_182_);
v___x_184_ = v_reuseFailAlloc_189_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = l_Lean_MessageData_ofSyntax(v_before_175_);
v___x_186_ = l_Lean_indentD(v___x_185_);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_184_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v_x_168_ = v___x_187_;
v_x_169_ = v_tail_171_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_opts_194_, lean_object* v_opt_195_){
_start:
{
lean_object* v_name_196_; lean_object* v_defValue_197_; lean_object* v_map_198_; lean_object* v___x_199_; 
v_name_196_ = lean_ctor_get(v_opt_195_, 0);
v_defValue_197_ = lean_ctor_get(v_opt_195_, 1);
v_map_198_ = lean_ctor_get(v_opts_194_, 0);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_198_, v_name_196_);
if (lean_obj_tag(v___x_199_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v_defValue_197_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v___x_199_);
if (lean_obj_tag(v_val_201_) == 1)
{
uint8_t v_v_202_; 
v_v_202_ = lean_ctor_get_uint8(v_val_201_, 0);
lean_dec_ref(v_val_201_);
return v_v_202_;
}
else
{
uint8_t v___x_203_; 
lean_dec(v_val_201_);
v___x_203_ = lean_unbox(v_defValue_197_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_204_, lean_object* v_opt_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_204_, v_opt_205_);
lean_dec_ref(v_opt_205_);
lean_dec_ref(v_opts_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_212_ = l_Lean_MessageData_ofFormat(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_213_, lean_object* v_macroStack_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_options_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_options_217_ = lean_ctor_get(v___y_215_, 2);
v___x_218_ = l_Lean_Elab_pp_macroStack;
v___x_219_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec(v_macroStack_214_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_msgData_213_);
return v___x_220_;
}
else
{
if (lean_obj_tag(v_macroStack_214_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_msgData_213_);
return v___x_221_;
}
else
{
lean_object* v_head_222_; lean_object* v_after_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_238_; 
v_head_222_ = lean_ctor_get(v_macroStack_214_, 0);
lean_inc(v_head_222_);
v_after_223_ = lean_ctor_get(v_head_222_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_head_222_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_head_222_, 0);
lean_dec(v_unused_239_);
v___x_225_ = v_head_222_;
v_isShared_226_ = v_isSharedCheck_238_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_after_223_);
lean_dec(v_head_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_238_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 7);
lean_ctor_set(v___x_225_, 1, v___x_227_);
lean_ctor_set(v___x_225_, 0, v_msgData_213_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_msgData_213_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_237_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_msgData_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_230_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_MessageData_ofSyntax(v_after_223_);
v___x_233_ = l_Lean_indentD(v___x_232_);
v_msgData_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_234_, 0, v___x_231_);
lean_ctor_set(v_msgData_234_, 1, v___x_233_);
v___x_235_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_234_, v_macroStack_214_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_240_, lean_object* v_macroStack_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_240_, v_macroStack_241_, v___y_242_);
lean_dec_ref(v___y_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; lean_object* v_env_252_; lean_object* v___x_253_; lean_object* v_mctx_254_; lean_object* v_lctx_255_; lean_object* v_options_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_251_ = lean_st_ref_get(v___y_249_);
v_env_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref(v_env_252_);
lean_dec(v___x_251_);
v___x_253_ = lean_st_ref_get(v___y_247_);
v_mctx_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_mctx_254_);
lean_dec(v___x_253_);
v_lctx_255_ = lean_ctor_get(v___y_246_, 2);
v_options_256_ = lean_ctor_get(v___y_248_, 2);
lean_inc_ref(v_options_256_);
lean_inc_ref(v_lctx_255_);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v_env_252_);
lean_ctor_set(v___x_257_, 1, v_mctx_254_);
lean_ctor_set(v___x_257_, 2, v_lctx_255_);
lean_ctor_set(v___x_257_, 3, v_options_256_);
v___x_258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_msgData_245_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v_macroStack_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_ref_275_ = lean_ctor_get(v___y_272_, 5);
v___x_276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_267_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v_macroStack_278_ = lean_ctor_get(v___y_268_, 1);
v___x_279_ = l_Lean_Elab_getBetterRef(v_ref_275_, v_macroStack_278_);
lean_inc(v_macroStack_278_);
v___x_280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_277_, v_macroStack_278_, v___y_272_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_279_);
lean_ctor_set(v___x_285_, 1, v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_as_305_, size_t v_sz_306_, size_t v_i_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_a_317_; uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_lt(v_i_307_, v_sz_306_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_b_308_);
return v___x_322_;
}
else
{
lean_object* v_array_323_; lean_object* v_start_324_; lean_object* v_stop_325_; uint8_t v___x_326_; 
v_array_323_ = lean_ctor_get(v_b_308_, 0);
v_start_324_ = lean_ctor_get(v_b_308_, 1);
v_stop_325_ = lean_ctor_get(v_b_308_, 2);
v___x_326_ = lean_nat_dec_lt(v_start_324_, v_stop_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_b_308_);
return v___x_327_;
}
else
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_356_; 
lean_inc(v_stop_325_);
lean_inc(v_start_324_);
lean_inc_ref(v_array_323_);
v_isSharedCheck_356_ = !lean_is_exclusive(v_b_308_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_357_ = lean_ctor_get(v_b_308_, 2);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_b_308_, 1);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_b_308_, 0);
lean_dec(v_unused_359_);
v___x_329_ = v_b_308_;
v_isShared_330_ = v_isSharedCheck_356_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_b_308_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_356_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v_a_331_ = lean_array_uget_borrowed(v_as_305_, v_i_307_);
v___x_332_ = lean_array_fget(v_array_323_, v_start_324_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_start_324_, v___x_333_);
lean_dec(v_start_324_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_334_);
v___x_336_ = v___x_329_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_array_323_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_stop_325_);
v___x_336_ = v_reuseFailAlloc_355_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_array_get_size(v_a_331_);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_nat_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v___x_332_);
v_a_317_ = v___x_336_;
goto v___jp_316_;
}
else
{
lean_object* v_declName_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_declName_340_ = lean_ctor_get(v___x_332_, 3);
lean_inc(v_declName_340_);
lean_dec(v___x_332_);
v___x_341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1);
v___x_342_ = l_Lean_MessageData_ofName(v_declName_340_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_345_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_dec_ref(v___x_346_);
v_a_317_ = v___x_336_;
goto v___jp_316_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___x_336_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
}
}
v___jp_316_:
{
size_t v___x_318_; size_t v___x_319_; 
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_307_, v___x_318_);
v_i_307_ = v___x_319_;
v_b_308_ = v_a_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_as_360_, lean_object* v_sz_361_, lean_object* v_i_362_, lean_object* v_b_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_361_);
lean_dec(v_sz_361_);
v_i_boxed_372_ = lean_unbox_usize(v_i_362_);
lean_dec(v_i_362_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_as_360_, v_sz_boxed_371_, v_i_boxed_372_, v_b_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v_as_360_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_a_374_, lean_object* v_as_375_, lean_object* v_i_376_, lean_object* v_j_377_, lean_object* v_bs_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_zero_384_; uint8_t v_isZero_385_; 
v_zero_384_ = lean_unsigned_to_nat(0u);
v_isZero_385_ = lean_nat_dec_eq(v_i_376_, v_zero_384_);
if (v_isZero_385_ == 1)
{
lean_object* v___x_386_; 
lean_dec(v_j_377_);
lean_dec(v_i_376_);
lean_dec_ref(v_a_374_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_bs_378_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_array_fget_borrowed(v_as_375_, v_j_377_);
lean_inc(v___x_387_);
lean_inc(v_j_377_);
lean_inc_ref(v_a_374_);
v___x_388_ = l_Lean_Elab_WF_varyingVarNames(v_a_374_, v_j_377_, v___x_387_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v_one_390_; lean_object* v_n_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref(v___x_388_);
v_one_390_ = lean_unsigned_to_nat(1u);
v_n_391_ = lean_nat_sub(v_i_376_, v_one_390_);
lean_dec(v_i_376_);
v___x_392_ = lean_nat_add(v_j_377_, v_one_390_);
lean_dec(v_j_377_);
v___x_393_ = lean_array_push(v_bs_378_, v_a_389_);
v_i_376_ = v_n_391_;
v_j_377_ = v___x_392_;
v_bs_378_ = v___x_393_;
goto _start;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_bs_378_);
lean_dec(v_j_377_);
lean_dec(v_i_376_);
lean_dec_ref(v_a_374_);
v_a_395_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_388_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_388_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_a_403_, lean_object* v_as_404_, lean_object* v_i_405_, lean_object* v_j_406_, lean_object* v_bs_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_403_, v_as_404_, v_i_405_, v_j_406_, v_bs_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec_ref(v_as_404_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object* v_as_414_, size_t v_sz_415_, size_t v_i_416_, lean_object* v_b_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_416_, v_sz_415_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_b_417_);
return v___x_422_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_424_; 
v_a_423_ = lean_array_uget_borrowed(v_as_414_, v_i_416_);
v___x_424_ = l_Lean_Elab_addAsAxiom___redArg(v_a_423_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_425_; size_t v___x_426_; size_t v___x_427_; 
lean_dec_ref(v___x_424_);
v___x_425_ = lean_box(0);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_416_, v___x_426_);
v_i_416_ = v___x_427_;
v_b_417_ = v___x_425_;
goto _start;
}
else
{
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_as_429_, lean_object* v_sz_430_, lean_object* v_i_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
size_t v_sz_boxed_436_; size_t v_i_boxed_437_; lean_object* v_res_438_; 
v_sz_boxed_436_ = lean_unbox_usize(v_sz_430_);
lean_dec(v_sz_430_);
v_i_boxed_437_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_429_, v_sz_boxed_436_, v_i_boxed_437_, v_b_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_as_429_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_442_ == 0)
{
return v_bs_441_;
}
else
{
lean_object* v_v_443_; lean_object* v_declName_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_v_443_ = lean_array_uget_borrowed(v_bs_441_, v_i_440_);
v_declName_444_ = lean_ctor_get(v_v_443_, 3);
lean_inc(v_declName_444_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_445_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_440_, v___x_447_);
v___x_449_ = lean_array_uset(v_bs_x27_446_, v_i_440_, v_declName_444_);
v_i_440_ = v___x_448_;
v_bs_441_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_bs_453_){
_start:
{
size_t v_sz_boxed_454_; size_t v_i_boxed_455_; lean_object* v_res_456_; 
v_sz_boxed_454_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_boxed_454_, v_i_boxed_455_, v_bs_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object* v_a_457_, lean_object* v___x_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_bs_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v___x_458_);
lean_dec_ref(v_a_457_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_bs_461_);
return v___x_466_;
}
else
{
lean_object* v_v_467_; lean_object* v_ref_468_; uint8_t v_kind_469_; lean_object* v_levelParams_470_; lean_object* v_modifiers_471_; lean_object* v_declName_472_; lean_object* v_binders_473_; lean_object* v_numSectionVars_474_; lean_object* v_type_475_; lean_object* v_value_476_; lean_object* v_termination_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_503_; 
v_v_467_ = lean_array_uget(v_bs_461_, v_i_460_);
v_ref_468_ = lean_ctor_get(v_v_467_, 0);
v_kind_469_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*9);
v_levelParams_470_ = lean_ctor_get(v_v_467_, 1);
v_modifiers_471_ = lean_ctor_get(v_v_467_, 2);
v_declName_472_ = lean_ctor_get(v_v_467_, 3);
v_binders_473_ = lean_ctor_get(v_v_467_, 4);
v_numSectionVars_474_ = lean_ctor_get(v_v_467_, 5);
v_type_475_ = lean_ctor_get(v_v_467_, 6);
v_value_476_ = lean_ctor_get(v_v_467_, 7);
v_termination_477_ = lean_ctor_get(v_v_467_, 8);
v_isSharedCheck_503_ = !lean_is_exclusive(v_v_467_);
if (v_isSharedCheck_503_ == 0)
{
v___x_479_ = v_v_467_;
v_isShared_480_ = v_isSharedCheck_503_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_termination_477_);
lean_inc(v_value_476_);
lean_inc(v_type_475_);
lean_inc(v_numSectionVars_474_);
lean_inc(v_binders_473_);
lean_inc(v_declName_472_);
lean_inc(v_modifiers_471_);
lean_inc(v_levelParams_470_);
lean_inc(v_ref_468_);
lean_dec(v_v_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_503_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_sz_481_ = lean_array_size(v_a_457_);
v___x_482_ = ((size_t)0ULL);
lean_inc_ref(v_a_457_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_481_, v___x_482_, v_a_457_);
lean_inc(v___x_458_);
v___x_484_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_483_, v___x_458_, v_value_476_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; lean_object* v___x_489_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_461_, v_i_460_, v___x_486_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 7, v_a_485_);
v___x_489_ = v___x_479_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_ref_468_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_levelParams_470_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_modifiers_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_declName_472_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_binders_473_);
lean_ctor_set(v_reuseFailAlloc_494_, 5, v_numSectionVars_474_);
lean_ctor_set(v_reuseFailAlloc_494_, 6, v_type_475_);
lean_ctor_set(v_reuseFailAlloc_494_, 7, v_a_485_);
lean_ctor_set(v_reuseFailAlloc_494_, 8, v_termination_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*9, v_kind_469_);
v___x_489_ = v_reuseFailAlloc_494_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_460_, v___x_490_);
v___x_492_ = lean_array_uset(v_bs_x27_487_, v_i_460_, v___x_489_);
v_i_460_ = v___x_491_;
v_bs_461_ = v___x_492_;
goto _start;
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_termination_477_);
lean_dec_ref(v_type_475_);
lean_dec(v_numSectionVars_474_);
lean_dec(v_binders_473_);
lean_dec(v_declName_472_);
lean_dec_ref(v_modifiers_471_);
lean_dec(v_levelParams_470_);
lean_dec(v_ref_468_);
lean_dec_ref(v_bs_461_);
lean_dec(v___x_458_);
lean_dec_ref(v_a_457_);
v_a_495_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_484_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_484_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object* v_a_504_, lean_object* v___x_505_, lean_object* v_sz_506_, lean_object* v_i_507_, lean_object* v_bs_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
size_t v_sz_boxed_512_; size_t v_i_boxed_513_; lean_object* v_res_514_; 
v_sz_boxed_512_ = lean_unbox_usize(v_sz_506_);
lean_dec(v_sz_506_);
v_i_boxed_513_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_504_, v___x_505_, v_sz_boxed_512_, v_i_boxed_513_, v_bs_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_515_, size_t v_sz_516_, size_t v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_a_515_, v_sz_516_, v___x_517_, v___x_518_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_527_);
lean_inc_ref(v_a_515_);
v___x_528_ = l_Lean_Elab_getFixedParamPerms(v_a_515_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_n(v_a_529_, 2);
lean_dec_ref(v___x_528_);
v___x_530_ = lean_array_get_size(v_a_515_);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_530_);
v___x_533_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_529_, v_a_515_, v___x_530_, v___x_531_, v___x_532_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; size_t v_sz_536_; lean_object* v___x_537_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref(v___x_533_);
lean_inc_ref(v_a_515_);
v___x_535_ = l_Array_toSubarray___redArg(v_a_515_, v___x_531_, v___x_530_);
v_sz_536_ = lean_array_size(v_a_534_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_534_, v_sz_536_, v___x_517_, v___x_535_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; lean_object* v_numSectionVars_539_; lean_object* v___x_540_; 
lean_dec_ref(v___x_537_);
v___x_538_ = lean_array_get_borrowed(v___x_519_, v_a_515_, v___x_531_);
v_numSectionVars_539_ = lean_ctor_get(v___x_538_, 5);
lean_inc(v_numSectionVars_539_);
lean_inc_ref(v_a_515_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_515_, v_numSectionVars_539_, v_sz_516_, v___x_517_, v_a_515_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref(v___x_540_);
lean_inc(v_a_534_);
lean_inc(v_a_529_);
v___x_542_ = l_Lean_Elab_WF_packMutual(v_a_529_, v_a_534_, v_a_541_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_552_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_552_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_534_);
lean_ctor_set(v___x_547_, 1, v_a_543_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_a_529_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_534_);
lean_dec(v_a_529_);
v_a_553_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_542_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_542_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_a_534_);
lean_dec(v_a_529_);
v_a_561_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_540_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_540_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_a_534_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_515_);
v_a_569_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_537_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_537_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_529_);
lean_dec_ref(v_a_515_);
v_a_577_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_533_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_533_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_a_515_);
v_a_585_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_528_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_528_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_a_515_);
v_a_593_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_527_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_527_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_601_, lean_object* v_sz_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v___x_46925__boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_602_);
lean_dec(v_sz_602_);
v___x_46925__boxed_614_ = lean_unbox_usize(v___x_603_);
lean_dec(v___x_603_);
v_res_615_ = l_Lean_Elab_wfRecursion___lam__0(v_a_601_, v_sz_boxed_613_, v___x_46925__boxed_614_, v___x_604_, v___x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v___x_605_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v___x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_options_627_; uint8_t v_hasTrace_628_; 
v_options_627_ = lean_ctor_get(v___y_624_, 2);
v_hasTrace_628_ = lean_ctor_get_uint8(v_options_627_, sizeof(void*)*1);
if (v_hasTrace_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v___x_619_);
v___x_629_ = lean_box(v_hasTrace_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v_inheritedTraceOptions_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_inheritedTraceOptions_631_ = lean_ctor_get(v___y_624_, 13);
v___x_632_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
v___x_633_ = l_Lean_Name_append(v___x_632_, v___x_619_);
v___x_634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_631_, v_options_627_, v___x_633_);
lean_dec(v___x_633_);
v___x_635_ = lean_box(v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v___x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Elab_wfRecursion___lam__1(v___x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v_snd_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_646_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_ref_655_; uint8_t v_kind_656_; lean_object* v_levelParams_657_; lean_object* v_modifiers_658_; lean_object* v_declName_659_; lean_object* v_binders_660_; lean_object* v_numSectionVars_661_; lean_object* v_type_662_; lean_object* v_value_663_; lean_object* v_termination_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v___x_654_);
v_ref_655_ = lean_ctor_get(v_snd_646_, 0);
v_kind_656_ = lean_ctor_get_uint8(v_snd_646_, sizeof(void*)*9);
v_levelParams_657_ = lean_ctor_get(v_snd_646_, 1);
v_modifiers_658_ = lean_ctor_get(v_snd_646_, 2);
v_declName_659_ = lean_ctor_get(v_snd_646_, 3);
v_binders_660_ = lean_ctor_get(v_snd_646_, 4);
v_numSectionVars_661_ = lean_ctor_get(v_snd_646_, 5);
v_type_662_ = lean_ctor_get(v_snd_646_, 6);
v_value_663_ = lean_ctor_get(v_snd_646_, 7);
v_termination_664_ = lean_ctor_get(v_snd_646_, 8);
v_isSharedCheck_690_ = !lean_is_exclusive(v_snd_646_);
if (v_isSharedCheck_690_ == 0)
{
v___x_666_ = v_snd_646_;
v_isShared_667_ = v_isSharedCheck_690_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_termination_664_);
lean_inc(v_value_663_);
lean_inc(v_type_662_);
lean_inc(v_numSectionVars_661_);
lean_inc(v_binders_660_);
lean_inc(v_declName_659_);
lean_inc(v_modifiers_658_);
lean_inc(v_levelParams_657_);
lean_inc(v_ref_655_);
lean_dec(v_snd_646_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_690_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Elab_WF_preprocess(v_value_663_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_681_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_681_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_681_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_681_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_expr_673_; lean_object* v___x_675_; 
v_expr_673_ = lean_ctor_get(v_a_669_, 0);
lean_inc_ref(v_expr_673_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 7, v_expr_673_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_ref_655_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_levelParams_657_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_modifiers_658_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_declName_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_binders_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v_numSectionVars_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_type_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_expr_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_termination_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*9, v_kind_656_);
v___x_675_ = v_reuseFailAlloc_680_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_a_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_676_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_666_);
lean_dec_ref(v_termination_664_);
lean_dec_ref(v_type_662_);
lean_dec(v_numSectionVars_661_);
lean_dec(v_binders_660_);
lean_dec(v_declName_659_);
lean_dec_ref(v_modifiers_658_);
lean_dec(v_levelParams_657_);
lean_dec(v_ref_655_);
v_a_682_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_668_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_668_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_snd_646_);
v_a_691_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_654_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_654_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v_snd_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Elab_wfRecursion___lam__2(v_snd_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v___y_715_, uint8_t v_suppressElabErrors_716_, lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_717_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_x_717_, 0);
switch(lean_obj_tag(v_pre_718_))
{
case 1:
{
lean_object* v_pre_719_; 
v_pre_719_ = lean_ctor_get(v_pre_718_, 0);
switch(lean_obj_tag(v_pre_719_))
{
case 0:
{
lean_object* v_str_720_; lean_object* v_str_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_str_720_ = lean_ctor_get(v_x_717_, 1);
v_str_721_ = lean_ctor_get(v_pre_718_, 1);
v___x_722_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_723_ = lean_string_dec_eq(v_str_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_725_ = lean_string_dec_eq(v_str_721_, v___x_724_);
if (v___x_725_ == 0)
{
return v___y_715_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_727_ = lean_string_dec_eq(v_str_720_, v___x_726_);
if (v___x_727_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_729_ = lean_string_dec_eq(v_str_720_, v___x_728_);
if (v___x_729_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
}
case 1:
{
lean_object* v_pre_730_; 
v_pre_730_ = lean_ctor_get(v_pre_719_, 0);
if (lean_obj_tag(v_pre_730_) == 0)
{
lean_object* v_str_731_; lean_object* v_str_732_; lean_object* v_str_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_str_731_ = lean_ctor_get(v_x_717_, 1);
v_str_732_ = lean_ctor_get(v_pre_718_, 1);
v_str_733_ = lean_ctor_get(v_pre_719_, 1);
v___x_734_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_735_ = lean_string_dec_eq(v_str_733_, v___x_734_);
if (v___x_735_ == 0)
{
return v___y_715_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_737_ = lean_string_dec_eq(v_str_732_, v___x_736_);
if (v___x_737_ == 0)
{
return v___y_715_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_739_ = lean_string_dec_eq(v_str_731_, v___x_738_);
if (v___x_739_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
}
}
else
{
return v___y_715_;
}
}
default: 
{
return v___y_715_;
}
}
}
case 0:
{
lean_object* v_str_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_str_740_ = lean_ctor_get(v_x_717_, 1);
v___x_741_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__0));
v___x_742_ = lean_string_dec_eq(v_str_740_, v___x_741_);
if (v___x_742_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
default: 
{
return v___y_715_;
}
}
}
else
{
return v___y_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v___y_743_, lean_object* v_suppressElabErrors_744_, lean_object* v_x_745_){
_start:
{
uint8_t v___y_47257__boxed_746_; uint8_t v_suppressElabErrors_boxed_747_; uint8_t v_res_748_; lean_object* v_r_749_; 
v___y_47257__boxed_746_ = lean_unbox(v___y_743_);
v_suppressElabErrors_boxed_747_ = lean_unbox(v_suppressElabErrors_744_);
v_res_748_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v___y_47257__boxed_746_, v_suppressElabErrors_boxed_747_, v_x_745_);
lean_dec(v_x_745_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_751_, lean_object* v_msgData_752_, uint8_t v_severity_753_, uint8_t v_isSilent_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; uint8_t v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_798_; uint8_t v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_823_; uint8_t v___y_824_; lean_object* v___y_825_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; lean_object* v___y_830_; lean_object* v___y_834_; uint8_t v___y_835_; uint8_t v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; uint8_t v___y_840_; uint8_t v___x_845_; lean_object* v___y_847_; uint8_t v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; uint8_t v___y_852_; uint8_t v___y_853_; uint8_t v___y_855_; uint8_t v___x_870_; 
v___x_845_ = 2;
v___x_870_ = l_Lean_instBEqMessageSeverity_beq(v_severity_753_, v___x_845_);
if (v___x_870_ == 0)
{
v___y_855_ = v___x_870_;
goto v___jp_854_;
}
else
{
uint8_t v___x_871_; 
lean_inc_ref(v_msgData_752_);
v___x_871_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_752_);
v___y_855_ = v___x_871_;
goto v___jp_854_;
}
v___jp_760_:
{
lean_object* v___x_770_; lean_object* v_currNamespace_771_; lean_object* v_openDecls_772_; lean_object* v_env_773_; lean_object* v_nextMacroScope_774_; lean_object* v_ngen_775_; lean_object* v_auxDeclNGen_776_; lean_object* v_traceState_777_; lean_object* v_cache_778_; lean_object* v_messages_779_; lean_object* v_infoState_780_; lean_object* v_snapshotTasks_781_; lean_object* v_newDecls_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_796_; 
v___x_770_ = lean_st_ref_take(v___y_769_);
v_currNamespace_771_ = lean_ctor_get(v___y_768_, 6);
v_openDecls_772_ = lean_ctor_get(v___y_768_, 7);
v_env_773_ = lean_ctor_get(v___x_770_, 0);
v_nextMacroScope_774_ = lean_ctor_get(v___x_770_, 1);
v_ngen_775_ = lean_ctor_get(v___x_770_, 2);
v_auxDeclNGen_776_ = lean_ctor_get(v___x_770_, 3);
v_traceState_777_ = lean_ctor_get(v___x_770_, 4);
v_cache_778_ = lean_ctor_get(v___x_770_, 5);
v_messages_779_ = lean_ctor_get(v___x_770_, 6);
v_infoState_780_ = lean_ctor_get(v___x_770_, 7);
v_snapshotTasks_781_ = lean_ctor_get(v___x_770_, 8);
v_newDecls_782_ = lean_ctor_get(v___x_770_, 9);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_796_ == 0)
{
v___x_784_ = v___x_770_;
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_newDecls_782_);
lean_inc(v_snapshotTasks_781_);
lean_inc(v_infoState_780_);
lean_inc(v_messages_779_);
lean_inc(v_cache_778_);
lean_inc(v_traceState_777_);
lean_inc(v_auxDeclNGen_776_);
lean_inc(v_ngen_775_);
lean_inc(v_nextMacroScope_774_);
lean_inc(v_env_773_);
lean_dec(v___x_770_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
lean_inc(v_openDecls_772_);
lean_inc(v_currNamespace_771_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_currNamespace_771_);
lean_ctor_set(v___x_786_, 1, v_openDecls_772_);
v___x_787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___y_767_);
lean_inc_ref(v___y_762_);
lean_inc_ref(v___y_763_);
v___x_788_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_788_, 0, v___y_763_);
lean_ctor_set(v___x_788_, 1, v___y_765_);
lean_ctor_set(v___x_788_, 2, v___y_764_);
lean_ctor_set(v___x_788_, 3, v___y_762_);
lean_ctor_set(v___x_788_, 4, v___x_787_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*5, v___y_761_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*5 + 1, v___y_766_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*5 + 2, v_isSilent_754_);
v___x_789_ = l_Lean_MessageLog_add(v___x_788_, v_messages_779_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 6, v___x_789_);
v___x_791_ = v___x_784_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_env_773_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_nextMacroScope_774_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_ngen_775_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_auxDeclNGen_776_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_traceState_777_);
lean_ctor_set(v_reuseFailAlloc_795_, 5, v_cache_778_);
lean_ctor_set(v_reuseFailAlloc_795_, 6, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_795_, 7, v_infoState_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 8, v_snapshotTasks_781_);
lean_ctor_set(v_reuseFailAlloc_795_, 9, v_newDecls_782_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = lean_st_ref_set(v___y_769_, v___x_791_);
v___x_793_ = lean_box(0);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
v___jp_797_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_821_; 
v___x_806_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_752_);
v___x_807_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_806_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_821_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_821_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_821_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_inc_ref_n(v___y_804_, 2);
v___x_812_ = l_Lean_FileMap_toPosition(v___y_804_, v___y_802_);
lean_dec(v___y_802_);
v___x_813_ = l_Lean_FileMap_toPosition(v___y_804_, v___y_805_);
lean_dec(v___y_805_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_800_ == 0)
{
lean_del_object(v___x_810_);
lean_dec_ref(v___y_798_);
v___y_761_ = v___y_799_;
v___y_762_ = v___x_815_;
v___y_763_ = v___y_801_;
v___y_764_ = v___x_814_;
v___y_765_ = v___x_812_;
v___y_766_ = v___y_803_;
v___y_767_ = v_a_808_;
v___y_768_ = v___y_757_;
v___y_769_ = v___y_758_;
goto v___jp_760_;
}
else
{
uint8_t v___x_816_; 
lean_inc(v_a_808_);
v___x_816_ = l_Lean_MessageData_hasTag(v___y_798_, v_a_808_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec_ref(v___x_814_);
lean_dec_ref(v___x_812_);
lean_dec(v_a_808_);
v___x_817_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_817_);
v___x_819_ = v___x_810_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_del_object(v___x_810_);
v___y_761_ = v___y_799_;
v___y_762_ = v___x_815_;
v___y_763_ = v___y_801_;
v___y_764_ = v___x_814_;
v___y_765_ = v___x_812_;
v___y_766_ = v___y_803_;
v___y_767_ = v_a_808_;
v___y_768_ = v___y_757_;
v___y_769_ = v___y_758_;
goto v___jp_760_;
}
}
}
}
v___jp_822_:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Syntax_getTailPos_x3f(v___y_825_, v___y_824_);
lean_dec(v___y_825_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_inc(v___y_830_);
v___y_798_ = v___y_823_;
v___y_799_ = v___y_824_;
v___y_800_ = v___y_826_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_830_;
v___y_803_ = v___y_829_;
v___y_804_ = v___y_828_;
v___y_805_ = v___y_830_;
goto v___jp_797_;
}
else
{
lean_object* v_val_832_; 
v_val_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_832_);
lean_dec_ref(v___x_831_);
v___y_798_ = v___y_823_;
v___y_799_ = v___y_824_;
v___y_800_ = v___y_826_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_830_;
v___y_803_ = v___y_829_;
v___y_804_ = v___y_828_;
v___y_805_ = v_val_832_;
goto v___jp_797_;
}
}
v___jp_833_:
{
lean_object* v_ref_841_; lean_object* v___x_842_; 
v_ref_841_ = l_Lean_replaceRef(v_ref_751_, v___y_837_);
v___x_842_ = l_Lean_Syntax_getPos_x3f(v_ref_841_, v___y_835_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_unsigned_to_nat(0u);
v___y_823_ = v___y_834_;
v___y_824_ = v___y_835_;
v___y_825_ = v_ref_841_;
v___y_826_ = v___y_836_;
v___y_827_ = v___y_838_;
v___y_828_ = v___y_839_;
v___y_829_ = v___y_840_;
v___y_830_ = v___x_843_;
goto v___jp_822_;
}
else
{
lean_object* v_val_844_; 
v_val_844_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_844_);
lean_dec_ref(v___x_842_);
v___y_823_ = v___y_834_;
v___y_824_ = v___y_835_;
v___y_825_ = v_ref_841_;
v___y_826_ = v___y_836_;
v___y_827_ = v___y_838_;
v___y_828_ = v___y_839_;
v___y_829_ = v___y_840_;
v___y_830_ = v_val_844_;
goto v___jp_822_;
}
}
v___jp_846_:
{
if (v___y_853_ == 0)
{
v___y_834_ = v___y_847_;
v___y_835_ = v___y_852_;
v___y_836_ = v___y_848_;
v___y_837_ = v___y_849_;
v___y_838_ = v___y_850_;
v___y_839_ = v___y_851_;
v___y_840_ = v_severity_753_;
goto v___jp_833_;
}
else
{
v___y_834_ = v___y_847_;
v___y_835_ = v___y_852_;
v___y_836_ = v___y_848_;
v___y_837_ = v___y_849_;
v___y_838_ = v___y_850_;
v___y_839_ = v___y_851_;
v___y_840_ = v___x_845_;
goto v___jp_833_;
}
}
v___jp_854_:
{
if (v___y_855_ == 0)
{
lean_object* v_fileName_856_; lean_object* v_fileMap_857_; lean_object* v_options_858_; lean_object* v_ref_859_; uint8_t v_suppressElabErrors_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___f_863_; uint8_t v___x_864_; uint8_t v___x_865_; 
v_fileName_856_ = lean_ctor_get(v___y_757_, 0);
v_fileMap_857_ = lean_ctor_get(v___y_757_, 1);
v_options_858_ = lean_ctor_get(v___y_757_, 2);
v_ref_859_ = lean_ctor_get(v___y_757_, 5);
v_suppressElabErrors_860_ = lean_ctor_get_uint8(v___y_757_, sizeof(void*)*14 + 1);
v___x_861_ = lean_box(v___y_855_);
v___x_862_ = lean_box(v_suppressElabErrors_860_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_863_, 0, v___x_861_);
lean_closure_set(v___f_863_, 1, v___x_862_);
v___x_864_ = 1;
v___x_865_ = l_Lean_instBEqMessageSeverity_beq(v_severity_753_, v___x_864_);
if (v___x_865_ == 0)
{
v___y_847_ = v___f_863_;
v___y_848_ = v_suppressElabErrors_860_;
v___y_849_ = v_ref_859_;
v___y_850_ = v_fileName_856_;
v___y_851_ = v_fileMap_857_;
v___y_852_ = v___y_855_;
v___y_853_ = v___x_865_;
goto v___jp_846_;
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = l_Lean_warningAsError;
v___x_867_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_858_, v___x_866_);
v___y_847_ = v___f_863_;
v___y_848_ = v_suppressElabErrors_860_;
v___y_849_ = v_ref_859_;
v___y_850_ = v_fileName_856_;
v___y_851_ = v_fileMap_857_;
v___y_852_ = v___y_855_;
v___y_853_ = v___x_867_;
goto v___jp_846_;
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec_ref(v_msgData_752_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_872_, lean_object* v_msgData_873_, lean_object* v_severity_874_, lean_object* v_isSilent_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v_severity_boxed_881_; uint8_t v_isSilent_boxed_882_; lean_object* v_res_883_; 
v_severity_boxed_881_ = lean_unbox(v_severity_874_);
v_isSilent_boxed_882_ = lean_unbox(v_isSilent_875_);
v_res_883_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_872_, v_msgData_873_, v_severity_boxed_881_, v_isSilent_boxed_882_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_ref_872_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_884_, lean_object* v_msgData_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = 1;
v___x_894_ = 0;
v___x_895_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_884_, v_msgData_885_, v___x_893_, v___x_894_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_896_, lean_object* v_msgData_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_896_, v_msgData_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v_ref_896_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v_as_914_, size_t v_i_915_, size_t v_stop_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_a_926_; uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_eq(v_i_915_, v_stop_916_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v_name_932_; lean_object* v_stx_933_; uint8_t v___y_935_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_931_ = lean_array_uget_borrowed(v_as_914_, v_i_915_);
v_name_932_ = lean_ctor_get(v___x_931_, 0);
v_stx_933_ = lean_ctor_get(v___x_931_, 1);
v___x_945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_946_ = lean_name_eq(v_name_932_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_948_ = lean_name_eq(v_name_932_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_box(0);
v_a_926_ = v___x_949_;
goto v___jp_925_;
}
else
{
v___y_935_ = v___x_948_;
goto v___jp_934_;
}
}
else
{
v___y_935_ = v___x_946_;
goto v___jp_934_;
}
v___jp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_932_);
v___x_937_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_932_, v___y_935_);
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
lean_dec_ref(v___x_937_);
v___x_939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_940_ = lean_string_append(v___x_938_, v___x_939_);
v___x_941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
v___x_942_ = l_Lean_MessageData_ofFormat(v___x_941_);
v___x_943_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_933_, v___x_942_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref(v___x_943_);
v_a_926_ = v_a_944_;
goto v___jp_925_;
}
else
{
return v___x_943_;
}
}
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_917_);
return v___x_950_;
}
v___jp_925_:
{
size_t v___x_927_; size_t v___x_928_; 
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_915_, v___x_927_);
v_i_915_ = v___x_928_;
v_b_917_ = v_a_926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v_as_951_, lean_object* v_i_952_, lean_object* v_stop_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
size_t v_i_boxed_962_; size_t v_stop_boxed_963_; lean_object* v_res_964_; 
v_i_boxed_962_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_stop_boxed_963_ = lean_unbox_usize(v_stop_953_);
lean_dec(v_stop_953_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_as_951_, v_i_boxed_962_, v_stop_boxed_963_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v_as_965_, size_t v_i_966_, size_t v_stop_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_a_977_; lean_object* v___y_982_; uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_eq(v_i_966_, v_stop_967_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v_modifiers_986_; lean_object* v_attrs_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_985_ = lean_array_uget_borrowed(v_as_965_, v_i_966_);
v_modifiers_986_ = lean_ctor_get(v___x_985_, 2);
v_attrs_987_ = lean_ctor_get(v_modifiers_986_, 2);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_array_get_size(v_attrs_987_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
if (v___x_991_ == 0)
{
v_a_977_ = v___x_990_;
goto v___jp_976_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = lean_nat_dec_le(v___x_989_, v___x_989_);
if (v___x_992_ == 0)
{
if (v___x_991_ == 0)
{
v_a_977_ = v___x_990_;
goto v___jp_976_;
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_989_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_987_, v___x_993_, v___x_994_, v___x_990_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
v___y_982_ = v___x_995_;
goto v___jp_981_;
}
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_989_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_987_, v___x_996_, v___x_997_, v___x_990_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
v___y_982_ = v___x_998_;
goto v___jp_981_;
}
}
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v_b_968_);
return v___x_999_;
}
v___jp_976_:
{
size_t v___x_978_; size_t v___x_979_; 
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_add(v_i_966_, v___x_978_);
v_i_966_ = v___x_979_;
v_b_968_ = v_a_977_;
goto _start;
}
v___jp_981_:
{
if (lean_obj_tag(v___y_982_) == 0)
{
lean_object* v_a_983_; 
v_a_983_ = lean_ctor_get(v___y_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___y_982_);
v_a_977_ = v_a_983_;
goto v___jp_976_;
}
else
{
return v___y_982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v_as_1000_, lean_object* v_i_1001_, lean_object* v_stop_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_i_boxed_1011_; size_t v_stop_boxed_1012_; lean_object* v_res_1013_; 
v_i_boxed_1011_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_stop_boxed_1012_ = lean_unbox_usize(v_stop_1002_);
lean_dec(v_stop_1002_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_as_1000_, v_i_boxed_1011_, v_stop_boxed_1012_, v_b_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_as_1000_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_bs_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1017_ == 0)
{
return v_bs_1016_;
}
else
{
lean_object* v_v_1018_; lean_object* v_termination_1019_; lean_object* v_decreasingBy_x3f_1020_; lean_object* v___x_1021_; lean_object* v_bs_x27_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v_v_1018_ = lean_array_uget_borrowed(v_bs_1016_, v_i_1015_);
v_termination_1019_ = lean_ctor_get(v_v_1018_, 8);
v_decreasingBy_x3f_1020_ = lean_ctor_get(v_termination_1019_, 4);
lean_inc(v_decreasingBy_x3f_1020_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v_bs_x27_1022_ = lean_array_uset(v_bs_1016_, v_i_1015_, v___x_1021_);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1015_, v___x_1023_);
v___x_1025_ = lean_array_uset(v_bs_x27_1022_, v_i_1015_, v_decreasingBy_x3f_1020_);
v_i_1015_ = v___x_1024_;
v_bs_1016_ = v___x_1025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_bs_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1030_, v_i_boxed_1031_, v_bs_1029_);
return v_res_1032_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1033_; double v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_float_of_nat(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_ref_1044_; lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1091_; 
v_ref_1044_ = lean_ctor_get(v___y_1041_, 5);
v___x_1045_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1091_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1091_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v_traceState_1051_; lean_object* v_env_1052_; lean_object* v_nextMacroScope_1053_; lean_object* v_ngen_1054_; lean_object* v_auxDeclNGen_1055_; lean_object* v_cache_1056_; lean_object* v_messages_1057_; lean_object* v_infoState_1058_; lean_object* v_snapshotTasks_1059_; lean_object* v_newDecls_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1090_; 
v___x_1050_ = lean_st_ref_take(v___y_1042_);
v_traceState_1051_ = lean_ctor_get(v___x_1050_, 4);
v_env_1052_ = lean_ctor_get(v___x_1050_, 0);
v_nextMacroScope_1053_ = lean_ctor_get(v___x_1050_, 1);
v_ngen_1054_ = lean_ctor_get(v___x_1050_, 2);
v_auxDeclNGen_1055_ = lean_ctor_get(v___x_1050_, 3);
v_cache_1056_ = lean_ctor_get(v___x_1050_, 5);
v_messages_1057_ = lean_ctor_get(v___x_1050_, 6);
v_infoState_1058_ = lean_ctor_get(v___x_1050_, 7);
v_snapshotTasks_1059_ = lean_ctor_get(v___x_1050_, 8);
v_newDecls_1060_ = lean_ctor_get(v___x_1050_, 9);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1062_ = v___x_1050_;
v_isShared_1063_ = v_isSharedCheck_1090_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_newDecls_1060_);
lean_inc(v_snapshotTasks_1059_);
lean_inc(v_infoState_1058_);
lean_inc(v_messages_1057_);
lean_inc(v_cache_1056_);
lean_inc(v_traceState_1051_);
lean_inc(v_auxDeclNGen_1055_);
lean_inc(v_ngen_1054_);
lean_inc(v_nextMacroScope_1053_);
lean_inc(v_env_1052_);
lean_dec(v___x_1050_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1090_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
uint64_t v_tid_1064_; lean_object* v_traces_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1089_; 
v_tid_1064_ = lean_ctor_get_uint64(v_traceState_1051_, sizeof(void*)*1);
v_traces_1065_ = lean_ctor_get(v_traceState_1051_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_traceState_1051_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1067_ = v_traceState_1051_;
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_traces_1065_);
lean_dec(v_traceState_1051_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; double v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1071_ = 0;
v___x_1072_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1073_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1073_, 0, v_cls_1037_);
lean_ctor_set(v___x_1073_, 1, v___x_1069_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
lean_ctor_set_float(v___x_1073_, sizeof(void*)*3, v___x_1070_);
lean_ctor_set_float(v___x_1073_, sizeof(void*)*3 + 8, v___x_1070_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*3 + 16, v___x_1071_);
v___x_1074_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1075_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v_a_1046_);
lean_ctor_set(v___x_1075_, 2, v___x_1074_);
lean_inc(v_ref_1044_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_ref_1044_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_PersistentArray_push___redArg(v_traces_1065_, v___x_1076_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1077_);
v___x_1079_ = v___x_1067_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1077_);
lean_ctor_set_uint64(v_reuseFailAlloc_1088_, sizeof(void*)*1, v_tid_1064_);
v___x_1079_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1079_);
v___x_1081_ = v___x_1062_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_env_1052_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_nextMacroScope_1053_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_ngen_1054_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_auxDeclNGen_1055_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1087_, 5, v_cache_1056_);
lean_ctor_set(v_reuseFailAlloc_1087_, 6, v_messages_1057_);
lean_ctor_set(v_reuseFailAlloc_1087_, 7, v_infoState_1058_);
lean_ctor_set(v_reuseFailAlloc_1087_, 8, v_snapshotTasks_1059_);
lean_ctor_set(v_reuseFailAlloc_1087_, 9, v_newDecls_1060_);
v___x_1081_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1082_ = lean_st_ref_set(v___y_1042_, v___x_1081_);
v___x_1083_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1083_);
v___x_1085_ = v___x_1048_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1092_, v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1103_, lean_object* v_snd_1104_, size_t v_sz_1105_, size_t v___x_1106_, lean_object* v_a_1107_, lean_object* v_fixedArgs_1108_, lean_object* v_fst_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v_wfRel_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v_a_1129_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_options_1279_; uint8_t v_hasTrace_1280_; 
v_options_1279_ = lean_ctor_get(v___y_1118_, 2);
v_hasTrace_1280_ = lean_ctor_get_uint8(v_options_1279_, sizeof(void*)*1);
if (v_hasTrace_1280_ == 0)
{
lean_dec(v___x_1112_);
v___y_1255_ = v___y_1114_;
v___y_1256_ = v___y_1115_;
v___y_1257_ = v___y_1116_;
v___y_1258_ = v___y_1117_;
v___y_1259_ = v___y_1118_;
v___y_1260_ = v___y_1119_;
goto v___jp_1254_;
}
else
{
lean_object* v_inheritedTraceOptions_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_inheritedTraceOptions_1281_ = lean_ctor_get(v___y_1118_, 13);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
lean_inc(v___x_1112_);
v___x_1283_ = l_Lean_Name_append(v___x_1282_, v___x_1112_);
v___x_1284_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1281_, v_options_1279_, v___x_1283_);
lean_dec(v___x_1283_);
if (v___x_1284_ == 0)
{
lean_dec(v___x_1112_);
v___y_1255_ = v___y_1114_;
v___y_1256_ = v___y_1115_;
v___y_1257_ = v___y_1116_;
v___y_1258_ = v___y_1117_;
v___y_1259_ = v___y_1118_;
v___y_1260_ = v___y_1119_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1113_);
v___x_1286_ = l_Lean_MessageData_ofExpr(v_wfRel_1113_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1112_, v___x_1287_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_dec_ref(v___x_1288_);
v___y_1255_ = v___y_1114_;
v___y_1256_ = v___y_1115_;
v___y_1257_ = v___y_1116_;
v___y_1258_ = v___y_1117_;
v___y_1259_ = v___y_1118_;
v___y_1260_ = v___y_1119_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
v___jp_1121_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v___x_1130_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1127_, v___y_1125_, v___y_1122_);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1130_, 0);
lean_dec(v_unused_1138_);
v___x_1132_ = v___x_1130_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 1);
lean_ctor_set(v___x_1132_, 0, v_a_1129_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
v___jp_1139_:
{
if (lean_obj_tag(v___y_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_env_1151_; lean_object* v___x_1152_; 
v_a_1148_ = lean_ctor_get(v___y_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___y_1147_);
v___x_1149_ = lean_st_ref_get(v___y_1141_);
v___x_1150_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1145_, v___y_1143_, v___y_1141_);
lean_dec_ref(v___x_1150_);
v_env_1151_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref_n(v_env_1151_, 2);
lean_dec(v___x_1149_);
v___x_1152_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1151_, v_a_1148_, v___y_1142_, v___y_1141_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1213_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1213_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1213_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v_env_1158_; lean_object* v_nextMacroScope_1159_; lean_object* v_ngen_1160_; lean_object* v_auxDeclNGen_1161_; lean_object* v_traceState_1162_; lean_object* v_messages_1163_; lean_object* v_infoState_1164_; lean_object* v_snapshotTasks_1165_; lean_object* v_newDecls_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1211_; 
v___x_1157_ = lean_st_ref_take(v___y_1141_);
v_env_1158_ = lean_ctor_get(v___x_1157_, 0);
v_nextMacroScope_1159_ = lean_ctor_get(v___x_1157_, 1);
v_ngen_1160_ = lean_ctor_get(v___x_1157_, 2);
v_auxDeclNGen_1161_ = lean_ctor_get(v___x_1157_, 3);
v_traceState_1162_ = lean_ctor_get(v___x_1157_, 4);
v_messages_1163_ = lean_ctor_get(v___x_1157_, 6);
v_infoState_1164_ = lean_ctor_get(v___x_1157_, 7);
v_snapshotTasks_1165_ = lean_ctor_get(v___x_1157_, 8);
v_newDecls_1166_ = lean_ctor_get(v___x_1157_, 9);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1157_, 5);
lean_dec(v_unused_1212_);
v___x_1168_ = v___x_1157_;
v_isShared_1169_ = v_isSharedCheck_1211_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_newDecls_1166_);
lean_inc(v_snapshotTasks_1165_);
lean_inc(v_infoState_1164_);
lean_inc(v_messages_1163_);
lean_inc(v_traceState_1162_);
lean_inc(v_auxDeclNGen_1161_);
lean_inc(v_ngen_1160_);
lean_inc(v_nextMacroScope_1159_);
lean_inc(v_env_1158_);
lean_dec(v___x_1157_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1211_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = l_Lean_copyExtraModUses(v_env_1151_, v_env_1158_);
v___x_1171_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 5, v___x_1171_);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_nextMacroScope_1159_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_ngen_1160_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_auxDeclNGen_1161_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_traceState_1162_);
lean_ctor_set(v_reuseFailAlloc_1210_, 5, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1210_, 6, v_messages_1163_);
lean_ctor_set(v_reuseFailAlloc_1210_, 7, v_infoState_1164_);
lean_ctor_set(v_reuseFailAlloc_1210_, 8, v_snapshotTasks_1165_);
lean_ctor_set(v_reuseFailAlloc_1210_, 9, v_newDecls_1166_);
v___x_1173_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_mctx_1176_; lean_object* v_zetaDeltaFVarIds_1177_; lean_object* v_postponed_1178_; lean_object* v_diag_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1208_; 
v___x_1174_ = lean_st_ref_set(v___y_1141_, v___x_1173_);
v___x_1175_ = lean_st_ref_take(v___y_1143_);
v_mctx_1176_ = lean_ctor_get(v___x_1175_, 0);
v_zetaDeltaFVarIds_1177_ = lean_ctor_get(v___x_1175_, 2);
v_postponed_1178_ = lean_ctor_get(v___x_1175_, 3);
v_diag_1179_ = lean_ctor_get(v___x_1175_, 4);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1175_, 1);
lean_dec(v_unused_1209_);
v___x_1181_ = v___x_1175_;
v_isShared_1182_ = v_isSharedCheck_1208_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_diag_1179_);
lean_inc(v_postponed_1178_);
lean_inc(v_zetaDeltaFVarIds_1177_);
lean_inc(v_mctx_1176_);
lean_dec(v___x_1175_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1208_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_mctx_1176_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_zetaDeltaFVarIds_1177_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_postponed_1178_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_diag_1179_);
v___x_1185_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v_ref_1187_; uint8_t v_kind_1188_; lean_object* v_levelParams_1189_; lean_object* v_modifiers_1190_; lean_object* v_declName_1191_; lean_object* v_binders_1192_; lean_object* v_numSectionVars_1193_; lean_object* v_type_1194_; lean_object* v_termination_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v___x_1186_ = lean_st_ref_set(v___y_1143_, v___x_1185_);
v_ref_1187_ = lean_ctor_get(v_fst_1103_, 0);
v_kind_1188_ = lean_ctor_get_uint8(v_fst_1103_, sizeof(void*)*9);
v_levelParams_1189_ = lean_ctor_get(v_fst_1103_, 1);
v_modifiers_1190_ = lean_ctor_get(v_fst_1103_, 2);
v_declName_1191_ = lean_ctor_get(v_fst_1103_, 3);
v_binders_1192_ = lean_ctor_get(v_fst_1103_, 4);
v_numSectionVars_1193_ = lean_ctor_get(v_fst_1103_, 5);
v_type_1194_ = lean_ctor_get(v_fst_1103_, 6);
v_termination_1195_ = lean_ctor_get(v_fst_1103_, 8);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_fst_1103_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_fst_1103_, 7);
lean_dec(v_unused_1206_);
v___x_1197_ = v_fst_1103_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_termination_1195_);
lean_inc(v_type_1194_);
lean_inc(v_numSectionVars_1193_);
lean_inc(v_binders_1192_);
lean_inc(v_declName_1191_);
lean_inc(v_modifiers_1190_);
lean_inc(v_levelParams_1189_);
lean_inc(v_ref_1187_);
lean_dec(v_fst_1103_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 7, v_a_1153_);
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_ref_1187_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_levelParams_1189_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_modifiers_1190_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_declName_1191_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_binders_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 5, v_numSectionVars_1193_);
lean_ctor_set(v_reuseFailAlloc_1204_, 6, v_type_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 7, v_a_1153_);
lean_ctor_set(v_reuseFailAlloc_1204_, 8, v_termination_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*9, v_kind_1188_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1200_);
v___x_1202_ = v___x_1155_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
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
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_env_1151_);
lean_dec_ref(v_fst_1103_);
v_a_1214_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1152_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1152_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; 
lean_dec_ref(v_fst_1103_);
v_a_1222_ = lean_ctor_get(v___y_1147_, 0);
lean_inc(v_a_1222_);
lean_dec_ref(v___y_1147_);
v___y_1122_ = v___y_1141_;
v___y_1123_ = v___y_1140_;
v___y_1124_ = v___y_1142_;
v___y_1125_ = v___y_1143_;
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1145_;
v___y_1128_ = v___y_1146_;
v_a_1129_ = v_a_1222_;
goto v___jp_1121_;
}
}
v___jp_1223_:
{
lean_object* v___x_1230_; lean_object* v_env_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_st_ref_get(v___y_1229_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1104_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v___x_1232_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1105_, v___x_1106_, v_a_1107_);
lean_inc_ref(v_fst_1103_);
v___x_1234_ = l_Lean_Elab_WF_mkFix(v_fst_1103_, v_fixedArgs_1108_, v_fst_1109_, v_wfRel_1113_, v___x_1110_, v___x_1233_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1235_, v___y_1228_, v___y_1229_);
v___y_1140_ = v___y_1226_;
v___y_1141_ = v___y_1229_;
v___y_1142_ = v___y_1228_;
v___y_1143_ = v___y_1227_;
v___y_1144_ = v___y_1224_;
v___y_1145_ = v_env_1231_;
v___y_1146_ = v___y_1225_;
v___y_1147_ = v___x_1236_;
goto v___jp_1139_;
}
else
{
v___y_1140_ = v___y_1226_;
v___y_1141_ = v___y_1229_;
v___y_1142_ = v___y_1228_;
v___y_1143_ = v___y_1227_;
v___y_1144_ = v___y_1224_;
v___y_1145_ = v_env_1231_;
v___y_1146_ = v___y_1225_;
v___y_1147_ = v___x_1234_;
goto v___jp_1139_;
}
}
else
{
lean_object* v_a_1237_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1237_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1232_);
v___y_1122_ = v___y_1229_;
v___y_1123_ = v___y_1226_;
v___y_1124_ = v___y_1228_;
v___y_1125_ = v___y_1227_;
v___y_1126_ = v___y_1224_;
v___y_1127_ = v_env_1231_;
v___y_1128_ = v___y_1225_;
v_a_1129_ = v_a_1237_;
goto v___jp_1121_;
}
}
v___jp_1238_:
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_dec_ref(v___y_1245_);
v___y_1224_ = v___y_1242_;
v___y_1225_ = v___y_1240_;
v___y_1226_ = v___y_1244_;
v___y_1227_ = v___y_1241_;
v___y_1228_ = v___y_1239_;
v___y_1229_ = v___y_1243_;
goto v___jp_1223_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1246_ = lean_ctor_get(v___y_1245_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___y_1245_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___y_1245_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___y_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
v___jp_1254_:
{
lean_object* v___x_1261_; 
lean_inc_ref(v_wfRel_1113_);
v___x_1261_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1113_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1261_);
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_array_get_size(v_a_1107_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_le(v___x_1264_, v___x_1264_);
if (v___x_1266_ == 0)
{
if (v___x_1265_ == 0)
{
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
goto v___jp_1223_;
}
else
{
size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_usize_of_nat(v___x_1264_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_1107_, v___x_1106_, v___x_1267_, v___x_1111_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
v___y_1239_ = v___y_1259_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1258_;
v___y_1242_ = v___y_1255_;
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1257_;
v___y_1245_ = v___x_1268_;
goto v___jp_1238_;
}
}
else
{
size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_usize_of_nat(v___x_1264_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_1107_, v___x_1106_, v___x_1269_, v___x_1111_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
v___y_1239_ = v___y_1259_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1258_;
v___y_1242_ = v___y_1255_;
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1257_;
v___y_1245_ = v___x_1270_;
goto v___jp_1238_;
}
}
}
else
{
lean_dec_ref(v_a_1262_);
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
goto v___jp_1223_;
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1271_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1261_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1261_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1297_ = _args[0];
lean_object* v_snd_1298_ = _args[1];
lean_object* v_sz_1299_ = _args[2];
lean_object* v___x_1300_ = _args[3];
lean_object* v_a_1301_ = _args[4];
lean_object* v_fixedArgs_1302_ = _args[5];
lean_object* v_fst_1303_ = _args[6];
lean_object* v___x_1304_ = _args[7];
lean_object* v___x_1305_ = _args[8];
lean_object* v___x_1306_ = _args[9];
lean_object* v_wfRel_1307_ = _args[10];
lean_object* v___y_1308_ = _args[11];
lean_object* v___y_1309_ = _args[12];
lean_object* v___y_1310_ = _args[13];
lean_object* v___y_1311_ = _args[14];
lean_object* v___y_1312_ = _args[15];
lean_object* v___y_1313_ = _args[16];
lean_object* v___y_1314_ = _args[17];
_start:
{
size_t v_sz_boxed_1315_; size_t v___x_47857__boxed_1316_; lean_object* v_res_1317_; 
v_sz_boxed_1315_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v___x_47857__boxed_1316_ = lean_unbox_usize(v___x_1300_);
lean_dec(v___x_1300_);
v_res_1317_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1297_, v_snd_1298_, v_sz_boxed_1315_, v___x_47857__boxed_1316_, v_a_1301_, v_fixedArgs_1302_, v_fst_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v_wfRel_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v_snd_1298_);
return v_res_1317_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1321_, size_t v___x_1322_, lean_object* v_a_1323_, lean_object* v_fst_1324_, lean_object* v_snd_1325_, lean_object* v_fst_1326_, lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_declName_1329_, lean_object* v_fst_1330_, lean_object* v_wf_1331_, lean_object* v_fixedArgs_1332_, lean_object* v_type_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Meta_whnfForall(v_type_1333_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; uint8_t v___x_1356_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v___x_1356_ = l_Lean_Expr_isForall(v_a_1342_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_fixedArgs_1332_);
lean_dec_ref(v_wf_1331_);
lean_dec_ref(v_fst_1330_);
lean_dec(v_declName_1329_);
lean_dec(v___x_1328_);
lean_dec_ref(v_fst_1326_);
lean_dec_ref(v_snd_1325_);
lean_dec_ref(v_fst_1324_);
lean_dec_ref(v_a_1323_);
v___x_1357_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1358_ = l_Lean_MessageData_ofExpr(v_a_1342_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1359_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
v___y_1344_ = v___y_1334_;
v___y_1345_ = v___y_1335_;
v___y_1346_ = v___y_1336_;
v___y_1347_ = v___y_1337_;
v___y_1348_ = v___y_1338_;
v___y_1349_ = v___y_1339_;
goto v___jp_1343_;
}
v___jp_1343_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; 
v___x_1350_ = l_Lean_Expr_bindingDomain_x21(v_a_1342_);
lean_dec(v_a_1342_);
lean_inc_ref(v_a_1323_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_1321_, v___x_1322_, v_a_1323_);
v___x_1352_ = lean_box_usize(v_sz_1321_);
v___x_1353_ = lean_box_usize(v___x_1322_);
lean_inc_ref(v___x_1351_);
lean_inc_ref(v_fst_1326_);
lean_inc_ref(v_fixedArgs_1332_);
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1354_, 0, v_fst_1324_);
lean_closure_set(v___f_1354_, 1, v_snd_1325_);
lean_closure_set(v___f_1354_, 2, v___x_1352_);
lean_closure_set(v___f_1354_, 3, v___x_1353_);
lean_closure_set(v___f_1354_, 4, v_a_1323_);
lean_closure_set(v___f_1354_, 5, v_fixedArgs_1332_);
lean_closure_set(v___f_1354_, 6, v_fst_1326_);
lean_closure_set(v___f_1354_, 7, v___x_1351_);
lean_closure_set(v___f_1354_, 8, v___x_1327_);
lean_closure_set(v___f_1354_, 9, v___x_1328_);
v___x_1355_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1351_, v_declName_1329_, v_fst_1330_, v_fixedArgs_1332_, v_fst_1326_, v___x_1350_, v_wf_1331_, v___f_1354_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v___x_1355_;
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_fixedArgs_1332_);
lean_dec_ref(v_wf_1331_);
lean_dec_ref(v_fst_1330_);
lean_dec(v_declName_1329_);
lean_dec(v___x_1328_);
lean_dec_ref(v_fst_1326_);
lean_dec_ref(v_snd_1325_);
lean_dec_ref(v_fst_1324_);
lean_dec_ref(v_a_1323_);
v_a_1369_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1341_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1341_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1377_ = _args[0];
lean_object* v___x_1378_ = _args[1];
lean_object* v_a_1379_ = _args[2];
lean_object* v_fst_1380_ = _args[3];
lean_object* v_snd_1381_ = _args[4];
lean_object* v_fst_1382_ = _args[5];
lean_object* v___x_1383_ = _args[6];
lean_object* v___x_1384_ = _args[7];
lean_object* v_declName_1385_ = _args[8];
lean_object* v_fst_1386_ = _args[9];
lean_object* v_wf_1387_ = _args[10];
lean_object* v_fixedArgs_1388_ = _args[11];
lean_object* v_type_1389_ = _args[12];
lean_object* v___y_1390_ = _args[13];
lean_object* v___y_1391_ = _args[14];
lean_object* v___y_1392_ = _args[15];
lean_object* v___y_1393_ = _args[16];
lean_object* v___y_1394_ = _args[17];
lean_object* v___y_1395_ = _args[18];
lean_object* v___y_1396_ = _args[19];
_start:
{
size_t v_sz_boxed_1397_; size_t v___x_48215__boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1377_);
lean_dec(v_sz_1377_);
v___x_48215__boxed_1398_ = lean_unbox_usize(v___x_1378_);
lean_dec(v___x_1378_);
v_res_1399_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1397_, v___x_48215__boxed_1398_, v_a_1379_, v_fst_1380_, v_snd_1381_, v_fst_1382_, v___x_1383_, v___x_1384_, v_declName_1385_, v_fst_1386_, v_wf_1387_, v_fixedArgs_1388_, v_type_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1400_, lean_object* v_fst_1401_, lean_object* v_fst_1402_, lean_object* v_fst_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Elab_WF_guessLex(v_a_1400_, v_fst_1401_, v_fst_1402_, v_fst_1403_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1412_, lean_object* v_fst_1413_, lean_object* v_fst_1414_, lean_object* v_fst_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1412_, v_fst_1413_, v_fst_1414_, v_fst_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1424_, uint8_t v_isExporting_1425_, lean_object* v___x_1426_, lean_object* v___y_1427_, lean_object* v___x_1428_, lean_object* v_a_x3f_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v_env_1432_; lean_object* v_nextMacroScope_1433_; lean_object* v_ngen_1434_; lean_object* v_auxDeclNGen_1435_; lean_object* v_traceState_1436_; lean_object* v_messages_1437_; lean_object* v_infoState_1438_; lean_object* v_snapshotTasks_1439_; lean_object* v_newDecls_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1465_; 
v___x_1431_ = lean_st_ref_take(v___y_1424_);
v_env_1432_ = lean_ctor_get(v___x_1431_, 0);
v_nextMacroScope_1433_ = lean_ctor_get(v___x_1431_, 1);
v_ngen_1434_ = lean_ctor_get(v___x_1431_, 2);
v_auxDeclNGen_1435_ = lean_ctor_get(v___x_1431_, 3);
v_traceState_1436_ = lean_ctor_get(v___x_1431_, 4);
v_messages_1437_ = lean_ctor_get(v___x_1431_, 6);
v_infoState_1438_ = lean_ctor_get(v___x_1431_, 7);
v_snapshotTasks_1439_ = lean_ctor_get(v___x_1431_, 8);
v_newDecls_1440_ = lean_ctor_get(v___x_1431_, 9);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1431_, 5);
lean_dec(v_unused_1466_);
v___x_1442_ = v___x_1431_;
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_newDecls_1440_);
lean_inc(v_snapshotTasks_1439_);
lean_inc(v_infoState_1438_);
lean_inc(v_messages_1437_);
lean_inc(v_traceState_1436_);
lean_inc(v_auxDeclNGen_1435_);
lean_inc(v_ngen_1434_);
lean_inc(v_nextMacroScope_1433_);
lean_inc(v_env_1432_);
lean_dec(v___x_1431_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = l_Lean_Environment_setExporting(v_env_1432_, v_isExporting_1425_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 5, v___x_1426_);
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_nextMacroScope_1433_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_ngen_1434_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_auxDeclNGen_1435_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_traceState_1436_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_messages_1437_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_infoState_1438_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_snapshotTasks_1439_);
lean_ctor_set(v_reuseFailAlloc_1464_, 9, v_newDecls_1440_);
v___x_1446_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_mctx_1449_; lean_object* v_zetaDeltaFVarIds_1450_; lean_object* v_postponed_1451_; lean_object* v_diag_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v___x_1447_ = lean_st_ref_set(v___y_1424_, v___x_1446_);
v___x_1448_ = lean_st_ref_take(v___y_1427_);
v_mctx_1449_ = lean_ctor_get(v___x_1448_, 0);
v_zetaDeltaFVarIds_1450_ = lean_ctor_get(v___x_1448_, 2);
v_postponed_1451_ = lean_ctor_get(v___x_1448_, 3);
v_diag_1452_ = lean_ctor_get(v___x_1448_, 4);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1448_, 1);
lean_dec(v_unused_1463_);
v___x_1454_ = v___x_1448_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_diag_1452_);
lean_inc(v_postponed_1451_);
lean_inc(v_zetaDeltaFVarIds_1450_);
lean_inc(v_mctx_1449_);
lean_dec(v___x_1448_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___x_1428_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_mctx_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_zetaDeltaFVarIds_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_postponed_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_diag_1452_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_st_ref_set(v___y_1427_, v___x_1457_);
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1467_, lean_object* v_isExporting_1468_, lean_object* v___x_1469_, lean_object* v___y_1470_, lean_object* v___x_1471_, lean_object* v_a_x3f_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_isExporting_boxed_1474_; lean_object* v_res_1475_; 
v_isExporting_boxed_1474_ = lean_unbox(v_isExporting_1468_);
v_res_1475_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1467_, v_isExporting_boxed_1474_, v___x_1469_, v___y_1470_, v___x_1471_, v_a_x3f_1472_);
lean_dec(v_a_x3f_1472_);
lean_dec(v___y_1470_);
lean_dec(v___y_1467_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1476_, uint8_t v_isExporting_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v_env_1486_; uint8_t v_isExporting_1487_; lean_object* v___x_1488_; lean_object* v_env_1489_; lean_object* v_nextMacroScope_1490_; lean_object* v_ngen_1491_; lean_object* v_auxDeclNGen_1492_; lean_object* v_traceState_1493_; lean_object* v_messages_1494_; lean_object* v_infoState_1495_; lean_object* v_snapshotTasks_1496_; lean_object* v_newDecls_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1551_; 
v___x_1485_ = lean_st_ref_get(v___y_1483_);
v_env_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_env_1486_);
lean_dec(v___x_1485_);
v_isExporting_1487_ = lean_ctor_get_uint8(v_env_1486_, sizeof(void*)*8);
lean_dec_ref(v_env_1486_);
v___x_1488_ = lean_st_ref_take(v___y_1483_);
v_env_1489_ = lean_ctor_get(v___x_1488_, 0);
v_nextMacroScope_1490_ = lean_ctor_get(v___x_1488_, 1);
v_ngen_1491_ = lean_ctor_get(v___x_1488_, 2);
v_auxDeclNGen_1492_ = lean_ctor_get(v___x_1488_, 3);
v_traceState_1493_ = lean_ctor_get(v___x_1488_, 4);
v_messages_1494_ = lean_ctor_get(v___x_1488_, 6);
v_infoState_1495_ = lean_ctor_get(v___x_1488_, 7);
v_snapshotTasks_1496_ = lean_ctor_get(v___x_1488_, 8);
v_newDecls_1497_ = lean_ctor_get(v___x_1488_, 9);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v___x_1488_, 5);
lean_dec(v_unused_1552_);
v___x_1499_ = v___x_1488_;
v_isShared_1500_ = v_isSharedCheck_1551_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_newDecls_1497_);
lean_inc(v_snapshotTasks_1496_);
lean_inc(v_infoState_1495_);
lean_inc(v_messages_1494_);
lean_inc(v_traceState_1493_);
lean_inc(v_auxDeclNGen_1492_);
lean_inc(v_ngen_1491_);
lean_inc(v_nextMacroScope_1490_);
lean_inc(v_env_1489_);
lean_dec(v___x_1488_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1551_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1501_ = l_Lean_Environment_setExporting(v_env_1489_, v_isExporting_1477_);
v___x_1502_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 5, v___x_1502_);
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_nextMacroScope_1490_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_ngen_1491_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_auxDeclNGen_1492_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_traceState_1493_);
lean_ctor_set(v_reuseFailAlloc_1550_, 5, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1550_, 6, v_messages_1494_);
lean_ctor_set(v_reuseFailAlloc_1550_, 7, v_infoState_1495_);
lean_ctor_set(v_reuseFailAlloc_1550_, 8, v_snapshotTasks_1496_);
lean_ctor_set(v_reuseFailAlloc_1550_, 9, v_newDecls_1497_);
v___x_1504_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_mctx_1507_; lean_object* v_zetaDeltaFVarIds_1508_; lean_object* v_postponed_1509_; lean_object* v_diag_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1548_; 
v___x_1505_ = lean_st_ref_set(v___y_1483_, v___x_1504_);
v___x_1506_ = lean_st_ref_take(v___y_1481_);
v_mctx_1507_ = lean_ctor_get(v___x_1506_, 0);
v_zetaDeltaFVarIds_1508_ = lean_ctor_get(v___x_1506_, 2);
v_postponed_1509_ = lean_ctor_get(v___x_1506_, 3);
v_diag_1510_ = lean_ctor_get(v___x_1506_, 4);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v___x_1506_, 1);
lean_dec(v_unused_1549_);
v___x_1512_ = v___x_1506_;
v_isShared_1513_ = v_isSharedCheck_1548_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_diag_1510_);
lean_inc(v_postponed_1509_);
lean_inc(v_zetaDeltaFVarIds_1508_);
lean_inc(v_mctx_1507_);
lean_dec(v___x_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1548_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 1, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_mctx_1507_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_zetaDeltaFVarIds_1508_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_postponed_1509_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_diag_1510_);
v___x_1516_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v_r_1518_; 
v___x_1517_ = lean_st_ref_set(v___y_1481_, v___x_1516_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v_r_1518_ = lean_apply_7(v_x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
if (lean_obj_tag(v_r_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1535_; 
v_a_1519_ = lean_ctor_get(v_r_1518_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_r_1518_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1521_ = v_r_1518_;
v_isShared_1522_ = v_isSharedCheck_1535_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v_r_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1535_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
lean_inc(v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set_tag(v___x_1521_, 1);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v___x_1525_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1483_, v_isExporting_1487_, v___x_1502_, v___y_1481_, v___x_1514_, v___x_1524_);
lean_dec_ref(v___x_1524_);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1525_, 0);
lean_dec(v_unused_1533_);
v___x_1527_ = v___x_1525_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v___x_1525_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_a_1519_);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1519_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1536_ = lean_ctor_get(v_r_1518_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v_r_1518_);
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1483_, v_isExporting_1487_, v___x_1502_, v___y_1481_, v___x_1514_, v___x_1537_);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v_a_1536_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1536_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1553_, lean_object* v_isExporting_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_isExporting_boxed_1562_; lean_object* v_res_1563_; 
v_isExporting_boxed_1562_ = lean_unbox(v_isExporting_1554_);
v_res_1563_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1553_, v_isExporting_boxed_1562_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1564_, uint8_t v_when_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
if (v_when_1565_ == 0)
{
lean_object* v___x_1573_; 
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
v___x_1573_ = lean_apply_7(v_x_1564_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, lean_box(0));
return v___x_1573_;
}
else
{
uint8_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = 0;
v___x_1575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1564_, v___x_1574_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1576_, lean_object* v_when_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v_when_boxed_1585_; lean_object* v_res_1586_; 
v_when_boxed_1585_ = lean_unbox(v_when_1577_);
v_res_1586_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1576_, v_when_boxed_1585_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t v_sz_1587_, size_t v_i_1588_, lean_object* v_bs_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_usize_dec_lt(v_i_1588_, v_sz_1587_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_bs_1589_);
return v___x_1594_;
}
else
{
lean_object* v_v_1595_; lean_object* v_ref_1596_; uint8_t v_kind_1597_; lean_object* v_levelParams_1598_; lean_object* v_modifiers_1599_; lean_object* v_declName_1600_; lean_object* v_binders_1601_; lean_object* v_numSectionVars_1602_; lean_object* v_type_1603_; lean_object* v_value_1604_; lean_object* v_termination_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1628_; 
v_v_1595_ = lean_array_uget(v_bs_1589_, v_i_1588_);
v_ref_1596_ = lean_ctor_get(v_v_1595_, 0);
v_kind_1597_ = lean_ctor_get_uint8(v_v_1595_, sizeof(void*)*9);
v_levelParams_1598_ = lean_ctor_get(v_v_1595_, 1);
v_modifiers_1599_ = lean_ctor_get(v_v_1595_, 2);
v_declName_1600_ = lean_ctor_get(v_v_1595_, 3);
v_binders_1601_ = lean_ctor_get(v_v_1595_, 4);
v_numSectionVars_1602_ = lean_ctor_get(v_v_1595_, 5);
v_type_1603_ = lean_ctor_get(v_v_1595_, 6);
v_value_1604_ = lean_ctor_get(v_v_1595_, 7);
v_termination_1605_ = lean_ctor_get(v_v_1595_, 8);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_v_1595_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1607_ = v_v_1595_;
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_termination_1605_);
lean_inc(v_value_1604_);
lean_inc(v_type_1603_);
lean_inc(v_numSectionVars_1602_);
lean_inc(v_binders_1601_);
lean_inc(v_declName_1600_);
lean_inc(v_modifiers_1599_);
lean_inc(v_levelParams_1598_);
lean_inc(v_ref_1596_);
lean_dec(v_v_1595_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Elab_WF_floatRecApp(v_value_1604_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v_bs_x27_1612_; lean_object* v___x_1614_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v_bs_x27_1612_ = lean_array_uset(v_bs_1589_, v_i_1588_, v___x_1611_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 7, v_a_1610_);
v___x_1614_ = v___x_1607_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_ref_1596_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_levelParams_1598_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_modifiers_1599_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_declName_1600_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_binders_1601_);
lean_ctor_set(v_reuseFailAlloc_1619_, 5, v_numSectionVars_1602_);
lean_ctor_set(v_reuseFailAlloc_1619_, 6, v_type_1603_);
lean_ctor_set(v_reuseFailAlloc_1619_, 7, v_a_1610_);
lean_ctor_set(v_reuseFailAlloc_1619_, 8, v_termination_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*9, v_kind_1597_);
v___x_1614_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1588_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1612_, v_i_1588_, v___x_1614_);
v_i_1588_ = v___x_1616_;
v_bs_1589_ = v___x_1617_;
goto _start;
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_del_object(v___x_1607_);
lean_dec_ref(v_termination_1605_);
lean_dec_ref(v_type_1603_);
lean_dec(v_numSectionVars_1602_);
lean_dec(v_binders_1601_);
lean_dec(v_declName_1600_);
lean_dec_ref(v_modifiers_1599_);
lean_dec(v_levelParams_1598_);
lean_dec(v_ref_1596_);
lean_dec_ref(v_bs_1589_);
v_a_1620_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1609_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1609_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* v_sz_1629_, lean_object* v_i_1630_, lean_object* v_bs_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
size_t v_sz_boxed_1635_; size_t v_i_boxed_1636_; lean_object* v_res_1637_; 
v_sz_boxed_1635_ = lean_unbox_usize(v_sz_1629_);
lean_dec(v_sz_1629_);
v_i_boxed_1636_ = lean_unbox_usize(v_i_1630_);
lean_dec(v_i_1630_);
v_res_1637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_1635_, v_i_boxed_1636_, v_bs_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_bs_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_bs_1640_);
return v___x_1642_;
}
else
{
lean_object* v_v_1643_; 
v_v_1643_ = lean_array_uget_borrowed(v_bs_1640_, v_i_1639_);
if (lean_obj_tag(v_v_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref(v_bs_1640_);
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1646_; lean_object* v_bs_x27_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v_val_1645_ = lean_ctor_get(v_v_1643_, 0);
lean_inc(v_val_1645_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v_bs_x27_1647_ = lean_array_uset(v_bs_1640_, v_i_1639_, v___x_1646_);
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_add(v_i_1639_, v___x_1648_);
v___x_1650_ = lean_array_uset(v_bs_x27_1647_, v_i_1639_, v_val_1645_);
v_i_1639_ = v___x_1649_;
v_bs_1640_ = v___x_1650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_sz_1652_, lean_object* v_i_1653_, lean_object* v_bs_1654_){
_start:
{
size_t v_sz_boxed_1655_; size_t v_i_boxed_1656_; lean_object* v_res_1657_; 
v_sz_boxed_1655_ = lean_unbox_usize(v_sz_1652_);
lean_dec(v_sz_1652_);
v_i_boxed_1656_ = lean_unbox_usize(v_i_1653_);
lean_dec(v_i_1653_);
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_boxed_1655_, v_i_boxed_1656_, v_bs_1654_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1658_, size_t v_i_1659_, lean_object* v_bs_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1659_, v_sz_1658_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_bs_1660_);
return v___x_1667_;
}
else
{
uint8_t v___x_1668_; lean_object* v_v_1669_; lean_object* v___x_1670_; 
v___x_1668_ = 0;
v_v_1669_ = lean_array_uget_borrowed(v_bs_1660_, v_i_1659_);
lean_inc(v_v_1669_);
v___x_1670_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1669_, v___x_1668_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; lean_object* v_bs_x27_1673_; size_t v___x_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = lean_unsigned_to_nat(0u);
v_bs_x27_1673_ = lean_array_uset(v_bs_1660_, v_i_1659_, v___x_1672_);
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1659_, v___x_1674_);
v___x_1676_ = lean_array_uset(v_bs_x27_1673_, v_i_1659_, v_a_1671_);
v_i_1659_ = v___x_1675_;
v_bs_1660_ = v___x_1676_;
goto _start;
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v_bs_1660_);
v_a_1678_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1670_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1670_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1686_, lean_object* v_i_1687_, lean_object* v_bs_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1686_);
lean_dec(v_sz_1686_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1694_, v_i_boxed_1695_, v_bs_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_env_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_env_1707_; lean_object* v_a_1709_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1706_ = lean_st_ref_get(v___y_1704_);
v_env_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc_ref(v_env_1707_);
lean_dec(v___x_1706_);
v___x_1719_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1697_, v___y_1702_, v___y_1704_);
lean_dec_ref(v___x_1719_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
v___x_1720_ = lean_apply_7(v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, lean_box(0));
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1707_, v___y_1702_, v___y_1704_);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1722_, 0);
lean_dec(v_unused_1730_);
v___x_1724_ = v___x_1722_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v___x_1722_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v_a_1721_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1721_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1731_; 
v_a_1731_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1720_);
v_a_1709_ = v_a_1731_;
goto v___jp_1708_;
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v___x_1710_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1707_, v___y_1702_, v___y_1704_);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v___x_1710_, 0);
lean_dec(v_unused_1718_);
v___x_1712_ = v___x_1710_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v___x_1710_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 1);
lean_ctor_set(v___x_1712_, 0, v_a_1709_);
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1709_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_env_1732_, lean_object* v_x_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_1732_, v_x_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1742_, lean_object* v_as_1743_, size_t v_sz_1744_, size_t v_i_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_a_1753_; uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_lt(v_i_1745_, v_sz_1744_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v___x_1742_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_b_1746_);
return v___x_1758_;
}
else
{
lean_object* v_a_1759_; uint8_t v_kind_1760_; lean_object* v_declName_1761_; lean_object* v_type_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_a_1759_ = lean_array_uget_borrowed(v_as_1743_, v_i_1745_);
v_kind_1760_ = lean_ctor_get_uint8(v_a_1759_, sizeof(void*)*9);
v_declName_1761_ = lean_ctor_get(v_a_1759_, 3);
v_type_1762_ = lean_ctor_get(v_a_1759_, 6);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_name_eq(v_declName_1761_, v___x_1742_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1760_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
lean_inc_ref(v_type_1762_);
v___x_1766_ = l_Lean_Meta_isProp(v_type_1762_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; uint8_t v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = lean_unbox(v_a_1767_);
lean_dec(v_a_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_inc(v___x_1742_);
lean_inc(v_a_1759_);
v___x_1769_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1759_, v___x_1742_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref(v___x_1769_);
v_a_1753_ = v___x_1763_;
goto v___jp_1752_;
}
else
{
lean_dec(v___x_1742_);
return v___x_1769_;
}
}
else
{
v_a_1753_ = v___x_1763_;
goto v___jp_1752_;
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v___x_1742_);
v_a_1770_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1766_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
v_a_1753_ = v___x_1763_;
goto v___jp_1752_;
}
}
else
{
v_a_1753_ = v___x_1763_;
goto v___jp_1752_;
}
}
v___jp_1752_:
{
size_t v___x_1754_; size_t v___x_1755_; 
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = lean_usize_add(v_i_1745_, v___x_1754_);
v_i_1745_ = v___x_1755_;
v_b_1746_ = v_a_1753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1778_, lean_object* v_as_1779_, lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1778_, v_as_1779_, v_sz_boxed_1788_, v_i_boxed_1789_, v_b_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec_ref(v_as_1779_);
return v_res_1790_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1808_ = l_Lean_stringToMessageData(v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1811_, lean_object* v_preDefs_1812_, lean_object* v_termMeasure_x3fs_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
size_t v_sz_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v_sz_1821_ = lean_array_size(v_preDefs_1812_);
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_1821_, v___x_1822_, v_preDefs_1812_, v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v_env_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; size_t v_sz_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___f_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_n(v_a_1824_, 2);
lean_dec_ref(v___x_1823_);
v___x_1825_ = lean_st_ref_get(v_a_1819_);
v_env_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_env_1826_);
lean_dec(v___x_1825_);
v___x_1827_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1828_ = lean_box(0);
v_sz_1842_ = lean_array_size(v_a_1824_);
v___x_1843_ = lean_box_usize(v_sz_1842_);
v___x_1844_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1845_, 0, v_a_1824_);
lean_closure_set(v___f_1845_, 1, v___x_1843_);
lean_closure_set(v___f_1845_, 2, v___x_1844_);
lean_closure_set(v___f_1845_, 3, v___x_1828_);
lean_closure_set(v___f_1845_, 4, v___x_1827_);
v___x_1846_ = l_Lean_Environment_unlockAsync(v_env_1826_);
v___x_1847_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1846_, v___f_1845_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_snd_1849_; lean_object* v_fst_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_2037_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v_snd_1849_ = lean_ctor_get(v_a_1848_, 1);
v_fst_1850_ = lean_ctor_get(v_a_1848_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_1848_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_1852_ = v_a_1848_;
v_isShared_1853_ = v_isSharedCheck_2037_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snd_1849_);
lean_inc(v_fst_1850_);
lean_dec(v_a_1848_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_2037_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_2036_; 
v_fst_1854_ = lean_ctor_get(v_snd_1849_, 0);
v_snd_1855_ = lean_ctor_get(v_snd_1849_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_snd_1849_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_1857_ = v_snd_1849_;
v_isShared_1858_ = v_isSharedCheck_2036_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_snd_1855_);
lean_inc(v_fst_1854_);
lean_dec(v_snd_1849_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_2036_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___x_1918_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v_wf_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___x_1964_; lean_object* v_a_1965_; lean_object* v___f_1966_; size_t v_sz_1967_; lean_object* v_termMeasures_x3f_1968_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; uint8_t v___x_2029_; 
v___x_1918_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_1964_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1918_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
lean_inc(v_snd_1855_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1966_, 0, v_snd_1855_);
v_sz_1967_ = lean_array_size(v_termMeasure_x3fs_1813_);
v_termMeasures_x3f_1968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_1967_, v___x_1822_, v_termMeasure_x3fs_1813_);
v___x_2029_ = lean_unbox(v_a_1965_);
lean_dec(v_a_1965_);
if (v___x_2029_ == 0)
{
v___y_1992_ = v_a_1814_;
v___y_1993_ = v_a_1815_;
v___y_1994_ = v_a_1816_;
v___y_1995_ = v_a_1817_;
v___y_1996_ = v_a_1818_;
v___y_1997_ = v_a_1819_;
goto v___jp_1991_;
}
else
{
lean_object* v_value_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_value_2030_ = lean_ctor_get(v_snd_1855_, 7);
v___x_2031_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2030_);
v___x_2032_ = l_Lean_MessageData_ofExpr(v_value_2030_);
v___x_2033_ = l_Lean_indentD(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2031_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1918_, v___x_2034_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_dec_ref(v___x_2035_);
v___y_1992_ = v_a_1814_;
v___y_1993_ = v_a_1815_;
v___y_1994_ = v_a_1816_;
v___y_1995_ = v_a_1817_;
v___y_1996_ = v_a_1818_;
v___y_1997_ = v_a_1819_;
goto v___jp_1991_;
}
else
{
lean_dec(v_termMeasures_x3f_1968_);
lean_dec_ref(v___f_1966_);
lean_del_object(v___x_1857_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
return v___x_2035_;
}
}
v___jp_1859_:
{
lean_object* v___x_1869_; 
lean_inc_ref(v___y_1862_);
lean_inc(v_a_1824_);
lean_inc(v_fst_1854_);
lean_inc(v_fst_1850_);
v___x_1869_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1850_, v_fst_1854_, v_a_1824_, v___y_1862_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1869_);
lean_inc_ref(v___y_1862_);
lean_inc(v_a_1824_);
lean_inc_ref(v_docCtx_1811_);
v___x_1871_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1811_, v_a_1824_, v_a_1870_, v___y_1862_, v___y_1861_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v_a_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1871_);
lean_inc(v_a_1824_);
v___x_1872_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1811_, v_a_1824_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref(v___x_1872_);
v___x_1873_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1855_, v___y_1861_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1842_, v___x_1822_, v_a_1824_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v_declName_1877_; lean_object* v___x_1878_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc_n(v_a_1876_, 2);
lean_dec_ref(v___x_1875_);
v_declName_1877_ = lean_ctor_get(v___y_1862_, 3);
lean_inc_n(v_declName_1877_, 2);
lean_dec_ref(v___y_1862_);
v___x_1878_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1876_, v_declName_1877_, v_fst_1850_, v_fst_1854_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_declName_1879_; lean_object* v_type_1880_; lean_object* v___x_1881_; 
lean_dec_ref(v___x_1878_);
v_declName_1879_ = lean_ctor_get(v_a_1874_, 3);
v_type_1880_ = lean_ctor_get(v_a_1874_, 6);
lean_inc(v_declName_1879_);
v___x_1881_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1879_, v___y_1868_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref(v___x_1881_);
lean_inc_ref(v_type_1880_);
v___x_1882_ = l_Lean_Meta_isProp(v_type_1880_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; uint8_t v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = lean_unbox(v_a_1883_);
lean_dec(v_a_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
lean_inc(v_declName_1877_);
v___x_1885_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1874_, v_declName_1877_, v___y_1860_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_dec_ref(v___x_1885_);
v___y_1830_ = v_a_1876_;
v___y_1831_ = v_declName_1877_;
v___y_1832_ = v___y_1863_;
v___y_1833_ = v___y_1864_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1866_;
v___y_1836_ = v___y_1867_;
v___y_1837_ = v___y_1868_;
goto v___jp_1829_;
}
else
{
lean_dec(v_declName_1877_);
lean_dec(v_a_1876_);
return v___x_1885_;
}
}
else
{
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1860_);
v___y_1830_ = v_a_1876_;
v___y_1831_ = v_declName_1877_;
v___y_1832_ = v___y_1863_;
v___y_1833_ = v___y_1864_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1866_;
v___y_1836_ = v___y_1867_;
v___y_1837_ = v___y_1868_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_declName_1877_);
lean_dec(v_a_1876_);
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1860_);
v_a_1886_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1882_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1882_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_dec(v_declName_1877_);
lean_dec(v_a_1876_);
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1860_);
return v___x_1881_;
}
}
else
{
lean_dec(v_declName_1877_);
lean_dec(v_a_1876_);
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1860_);
return v___x_1878_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec(v_fst_1854_);
lean_dec(v_fst_1850_);
v_a_1894_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1875_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1875_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec(v_fst_1854_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
v_a_1902_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1873_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1873_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
return v___x_1872_;
}
}
else
{
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
return v___x_1871_;
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
v_a_1910_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1869_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1869_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
v___jp_1919_:
{
lean_object* v_declName_1929_; lean_object* v_type_1930_; lean_object* v_numFixed_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; 
v_declName_1929_ = lean_ctor_get(v_snd_1855_, 3);
v_type_1930_ = lean_ctor_get(v_snd_1855_, 6);
v_numFixed_1931_ = lean_ctor_get(v_fst_1850_, 0);
v___x_1932_ = lean_box_usize(v_sz_1842_);
v___x_1933_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1850_);
lean_inc(v_declName_1929_);
lean_inc(v_fst_1854_);
lean_inc(v_snd_1855_);
lean_inc(v_a_1824_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1934_, 0, v___x_1932_);
lean_closure_set(v___f_1934_, 1, v___x_1933_);
lean_closure_set(v___f_1934_, 2, v_a_1824_);
lean_closure_set(v___f_1934_, 3, v___y_1920_);
lean_closure_set(v___f_1934_, 4, v_snd_1855_);
lean_closure_set(v___f_1934_, 5, v_fst_1854_);
lean_closure_set(v___f_1934_, 6, v___x_1828_);
lean_closure_set(v___f_1934_, 7, v___x_1918_);
lean_closure_set(v___f_1934_, 8, v_declName_1929_);
lean_closure_set(v___f_1934_, 9, v_fst_1850_);
lean_closure_set(v___f_1934_, 10, v_wf_1922_);
lean_inc(v_numFixed_1931_);
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_numFixed_1931_);
v___x_1936_ = 0;
lean_inc_ref(v_type_1930_);
v___x_1937_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1930_, v___x_1935_, v___f_1934_, v___x_1936_, v___x_1936_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; uint8_t v___x_1941_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v___x_1939_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1918_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
if (v___x_1941_ == 0)
{
lean_del_object(v___x_1857_);
lean_del_object(v___x_1852_);
v___y_1860_ = v___y_1921_;
v___y_1861_ = v___x_1936_;
v___y_1862_ = v_a_1938_;
v___y_1863_ = v___y_1923_;
v___y_1864_ = v___y_1924_;
v___y_1865_ = v___y_1925_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v___y_1927_;
v___y_1868_ = v___y_1928_;
goto v___jp_1859_;
}
else
{
lean_object* v_declName_1942_; lean_object* v_value_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v_declName_1942_ = lean_ctor_get(v_a_1938_, 3);
v_value_1943_ = lean_ctor_get(v_a_1938_, 7);
v___x_1944_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1942_);
v___x_1945_ = l_Lean_MessageData_ofName(v_declName_1942_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 7);
lean_ctor_set(v___x_1857_, 1, v___x_1945_);
lean_ctor_set(v___x_1857_, 0, v___x_1944_);
v___x_1947_ = v___x_1857_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 7);
lean_ctor_set(v___x_1852_, 1, v___x_1948_);
lean_ctor_set(v___x_1852_, 0, v___x_1947_);
v___x_1950_ = v___x_1852_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_inc_ref(v_value_1943_);
v___x_1951_ = l_Lean_MessageData_ofExpr(v_value_1943_);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1918_, v___x_1952_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_dec_ref(v___x_1953_);
v___y_1860_ = v___y_1921_;
v___y_1861_ = v___x_1936_;
v___y_1862_ = v_a_1938_;
v___y_1863_ = v___y_1923_;
v___y_1864_ = v___y_1924_;
v___y_1865_ = v___y_1925_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v___y_1927_;
v___y_1868_ = v___y_1928_;
goto v___jp_1859_;
}
else
{
lean_dec(v_a_1938_);
lean_dec_ref(v___y_1921_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
return v___x_1953_;
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___y_1921_);
lean_del_object(v___x_1857_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
v_a_1956_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1937_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1937_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
v___jp_1969_:
{
if (lean_obj_tag(v_termMeasures_x3f_1968_) == 1)
{
lean_object* v_val_1979_; 
lean_dec_ref(v___y_1972_);
v_val_1979_ = lean_ctor_get(v_termMeasures_x3f_1968_, 0);
lean_inc(v_val_1979_);
lean_dec_ref(v_termMeasures_x3f_1968_);
v___y_1920_ = v___y_1970_;
v___y_1921_ = v___y_1971_;
v_wf_1922_ = v_val_1979_;
v___y_1923_ = v___y_1973_;
v___y_1924_ = v___y_1974_;
v___y_1925_ = v___y_1975_;
v___y_1926_ = v___y_1976_;
v___y_1927_ = v___y_1977_;
v___y_1928_ = v___y_1978_;
goto v___jp_1919_;
}
else
{
uint8_t v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v_termMeasures_x3f_1968_);
v___x_1980_ = 1;
v___x_1981_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1972_, v___x_1980_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1981_);
v___y_1920_ = v___y_1970_;
v___y_1921_ = v___y_1971_;
v_wf_1922_ = v_a_1982_;
v___y_1923_ = v___y_1973_;
v___y_1924_ = v___y_1974_;
v___y_1925_ = v___y_1975_;
v___y_1926_ = v___y_1976_;
v___y_1927_ = v___y_1977_;
v___y_1928_ = v___y_1978_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_del_object(v___x_1857_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
v_a_1983_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
v___jp_1991_:
{
lean_object* v___x_1998_; lean_object* v_env_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1998_ = lean_st_ref_get(v___y_1997_);
v_env_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_ref(v_env_1999_);
lean_dec(v___x_1998_);
v___x_2000_ = l_Lean_Environment_unlockAsync(v_env_1999_);
v___x_2001_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_2000_, v___f_1966_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2020_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_2001_);
v_fst_2003_ = lean_ctor_get(v_a_2002_, 0);
v_snd_2004_ = lean_ctor_get(v_a_2002_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2006_ = v_a_2002_;
v_isShared_2007_ = v_isSharedCheck_2020_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2004_);
lean_inc(v_fst_2003_);
lean_dec(v_a_2002_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2020_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v_a_2009_; lean_object* v___f_2010_; uint8_t v___x_2011_; 
v___x_2008_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1918_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2008_);
lean_inc(v_fst_1854_);
lean_inc(v_fst_1850_);
lean_inc(v_fst_2003_);
lean_inc(v_a_1824_);
v___f_2010_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2010_, 0, v_a_1824_);
lean_closure_set(v___f_2010_, 1, v_fst_2003_);
lean_closure_set(v___f_2010_, 2, v_fst_1850_);
lean_closure_set(v___f_2010_, 3, v_fst_1854_);
v___x_2011_ = lean_unbox(v_a_2009_);
lean_dec(v_a_2009_);
if (v___x_2011_ == 0)
{
lean_del_object(v___x_2006_);
v___y_1970_ = v_fst_2003_;
v___y_1971_ = v_snd_2004_;
v___y_1972_ = v___f_2010_;
v___y_1973_ = v___y_1992_;
v___y_1974_ = v___y_1993_;
v___y_1975_ = v___y_1994_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v___y_1996_;
v___y_1978_ = v___y_1997_;
goto v___jp_1969_;
}
else
{
lean_object* v_value_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v_value_2012_ = lean_ctor_get(v_snd_1855_, 7);
v___x_2013_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2012_);
v___x_2014_ = l_Lean_MessageData_ofExpr(v_value_2012_);
v___x_2015_ = l_Lean_indentD(v___x_2014_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 7);
lean_ctor_set(v___x_2006_, 1, v___x_2015_);
lean_ctor_set(v___x_2006_, 0, v___x_2013_);
v___x_2017_ = v___x_2006_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1918_, v___x_2017_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_dec_ref(v___x_2018_);
v___y_1970_ = v_fst_2003_;
v___y_1971_ = v_snd_2004_;
v___y_1972_ = v___f_2010_;
v___y_1973_ = v___y_1992_;
v___y_1974_ = v___y_1993_;
v___y_1975_ = v___y_1994_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v___y_1996_;
v___y_1978_ = v___y_1997_;
goto v___jp_1969_;
}
else
{
lean_dec_ref(v___f_2010_);
lean_dec(v_snd_2004_);
lean_dec(v_fst_2003_);
lean_dec(v_termMeasures_x3f_1968_);
lean_del_object(v___x_1857_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_termMeasures_x3f_1968_);
lean_del_object(v___x_1857_);
lean_dec(v_snd_1855_);
lean_dec(v_fst_1854_);
lean_del_object(v___x_1852_);
lean_dec(v_fst_1850_);
lean_dec(v_a_1824_);
lean_dec_ref(v_docCtx_1811_);
v_a_2021_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2001_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2001_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_1824_);
lean_dec_ref(v_termMeasure_x3fs_1813_);
lean_dec_ref(v_docCtx_1811_);
v_a_2038_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1847_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1847_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
v___jp_1829_:
{
size_t v_sz_1838_; lean_object* v___x_1839_; 
v_sz_1838_ = lean_array_size(v___y_1830_);
lean_inc(v___y_1831_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1831_, v___y_1830_, v_sz_1838_, v___x_1822_, v___x_1828_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___x_1840_; 
lean_dec_ref(v___x_1839_);
v___x_1840_ = l_Lean_enableRealizationsForConst(v___y_1831_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1841_; 
lean_dec_ref(v___x_1840_);
v___x_1841_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1830_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1841_;
}
else
{
lean_dec_ref(v___y_1830_);
return v___x_1840_;
}
}
else
{
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v___x_1839_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec_ref(v_termMeasure_x3fs_1813_);
lean_dec_ref(v_docCtx_1811_);
v_a_2046_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1823_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1823_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2054_, lean_object* v_preDefs_2055_, lean_object* v_termMeasure_x3fs_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Elab_wfRecursion(v_docCtx_2054_, v_preDefs_2055_, v_termMeasure_x3fs_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2065_, lean_object* v_msg_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2075_, lean_object* v_msg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2075_, v_msg_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_bs_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_2085_, v_i_2086_, v_bs_2087_, v___y_2092_, v___y_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_2096_, lean_object* v_i_2097_, lean_object* v_bs_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
size_t v_sz_boxed_2106_; size_t v_i_boxed_2107_; lean_object* v_res_2108_; 
v_sz_boxed_2106_ = lean_unbox_usize(v_sz_2096_);
lean_dec(v_sz_2096_);
v_i_boxed_2107_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_2106_, v_i_boxed_2107_, v_bs_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object* v_as_2109_, size_t v_sz_2110_, size_t v_i_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2109_, v_sz_2110_, v_i_2111_, v_b_2112_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_as_2121_, lean_object* v_sz_2122_, lean_object* v_i_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
size_t v_sz_boxed_2132_; size_t v_i_boxed_2133_; lean_object* v_res_2134_; 
v_sz_boxed_2132_ = lean_unbox_usize(v_sz_2122_);
lean_dec(v_sz_2122_);
v_i_boxed_2133_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_2121_, v_sz_boxed_2132_, v_i_boxed_2133_, v_b_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_as_2121_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_a_2135_, lean_object* v_as_2136_, lean_object* v_i_2137_, lean_object* v_j_2138_, lean_object* v_inv_2139_, lean_object* v_bs_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_2135_, v_as_2136_, v_i_2137_, v_j_2138_, v_bs_2140_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_a_2149_, lean_object* v_as_2150_, lean_object* v_i_2151_, lean_object* v_j_2152_, lean_object* v_inv_2153_, lean_object* v_bs_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(v_a_2149_, v_as_2150_, v_i_2151_, v_j_2152_, v_inv_2153_, v_bs_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v_as_2150_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object* v_a_2163_, lean_object* v___x_2164_, size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_bs_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2163_, v___x_2164_, v_sz_2165_, v_i_2166_, v_bs_2167_, v___y_2172_, v___y_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_a_2176_, lean_object* v___x_2177_, lean_object* v_sz_2178_, lean_object* v_i_2179_, lean_object* v_bs_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
size_t v_sz_boxed_2188_; size_t v_i_boxed_2189_; lean_object* v_res_2190_; 
v_sz_boxed_2188_ = lean_unbox_usize(v_sz_2178_);
lean_dec(v_sz_2178_);
v_i_boxed_2189_ = lean_unbox_usize(v_i_2179_);
lean_dec(v_i_2179_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_2176_, v___x_2177_, v_sz_boxed_2188_, v_i_boxed_2189_, v_bs_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_00_u03b1_2191_, lean_object* v_env_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_2192_, v_x_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_env_2203_, lean_object* v_x_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(v_00_u03b1_2202_, v_env_2203_, v_x_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2213_, lean_object* v_msg_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2213_, v_msg_2214_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2223_, lean_object* v_msg_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2223_, v_msg_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2233_, size_t v_i_2234_, lean_object* v_bs_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2233_, v_i_2234_, v_bs_2235_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2244_, lean_object* v_i_2245_, lean_object* v_bs_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
size_t v_sz_boxed_2254_; size_t v_i_boxed_2255_; lean_object* v_res_2256_; 
v_sz_boxed_2254_ = lean_unbox_usize(v_sz_2244_);
lean_dec(v_sz_2244_);
v_i_boxed_2255_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_res_2256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2254_, v_i_boxed_2255_, v_bs_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2257_, lean_object* v_as_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2257_, v_as_2258_, v_sz_2259_, v_i_2260_, v_b_2261_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2270_, lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
size_t v_sz_boxed_2282_; size_t v_i_boxed_2283_; lean_object* v_res_2284_; 
v_sz_boxed_2282_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2283_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2270_, v_as_2271_, v_sz_boxed_2282_, v_i_boxed_2283_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec_ref(v_as_2271_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2285_, lean_object* v_x_2286_, uint8_t v_isExporting_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2286_, v_isExporting_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_x_2297_, lean_object* v_isExporting_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v_isExporting_boxed_2306_; lean_object* v_res_2307_; 
v_isExporting_boxed_2306_ = lean_unbox(v_isExporting_2298_);
v_res_2307_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2296_, v_x_2297_, v_isExporting_boxed_2306_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2308_, lean_object* v_x_2309_, uint8_t v_when_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2309_, v_when_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_x_2320_, lean_object* v_when_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v_when_boxed_2329_; lean_object* v_res_2330_; 
v_when_boxed_2329_ = lean_unbox(v_when_2321_);
v_res_2330_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2319_, v_x_2320_, v_when_boxed_2329_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2331_, lean_object* v_macroStack_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2331_, v_macroStack_2332_, v___y_2337_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2341_, lean_object* v_macroStack_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2341_, v_macroStack_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2351_, lean_object* v_msgData_2352_, uint8_t v_severity_2353_, uint8_t v_isSilent_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2351_, v_msgData_2352_, v_severity_2353_, v_isSilent_2354_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2363_, lean_object* v_msgData_2364_, lean_object* v_severity_2365_, lean_object* v_isSilent_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_severity_boxed_2374_; uint8_t v_isSilent_boxed_2375_; lean_object* v_res_2376_; 
v_severity_boxed_2374_ = lean_unbox(v_severity_2365_);
v_isSilent_boxed_2375_ = lean_unbox(v_isSilent_2366_);
v_res_2376_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2363_, v_msgData_2364_, v_severity_boxed_2374_, v_isSilent_boxed_2375_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_ref_2363_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2447_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2448_ = 0;
v___x_2449_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2450_ = l_Lean_registerTraceClass(v___x_2447_, v___x_2448_, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2452_;
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
