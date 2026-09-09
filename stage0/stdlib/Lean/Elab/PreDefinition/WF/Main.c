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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_26_ = lean_st_ref_put(v___y_10_, v___x_25_);
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
v___x_38_ = lean_st_ref_put(v___y_9_, v___x_37_);
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
lean_dec_ref_known(v___x_198_, 1);
if (lean_obj_tag(v_val_200_) == 1)
{
uint8_t v_v_201_; 
v_v_201_ = lean_ctor_get_uint8(v_val_200_, 0);
lean_dec_ref_known(v_val_200_, 0);
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
v_options_216_ = lean_ctor_get(v___y_214_, 1);
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
v_options_255_ = lean_ctor_get(v___y_247_, 1);
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
v_ref_274_ = lean_ctor_get(v___y_271_, 4);
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
lean_dec_ref_known(v___x_345_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_a_373_, size_t v_sz_374_, size_t v_i_375_, lean_object* v_bs_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v_a_373_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_bs_376_);
return v___x_383_;
}
else
{
lean_object* v_v_384_; lean_object* v___x_385_; lean_object* v_bs_x27_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_v_384_ = lean_array_uget(v_bs_376_, v_i_375_);
v___x_385_ = lean_unsigned_to_nat(0u);
v_bs_x27_386_ = lean_array_uset(v_bs_376_, v_i_375_, v___x_385_);
v___x_387_ = lean_usize_to_nat(v_i_375_);
lean_inc_ref(v_a_373_);
v___x_388_ = l_Lean_Elab_WF_varyingVarNames(v_a_373_, v___x_387_, v_v_384_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_add(v_i_375_, v___x_390_);
v___x_392_ = lean_array_uset(v_bs_x27_386_, v_i_375_, v_a_389_);
v_i_375_ = v___x_391_;
v_bs_376_ = v___x_392_;
goto _start;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v_bs_x27_386_);
lean_dec_ref(v_a_373_);
v_a_394_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_388_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_388_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_a_402_, lean_object* v_sz_403_, lean_object* v_i_404_, lean_object* v_bs_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v_sz_boxed_411_ = lean_unbox_usize(v_sz_403_);
lean_dec(v_sz_403_);
v_i_boxed_412_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_402_, v_sz_boxed_411_, v_i_boxed_412_, v_bs_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
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
lean_dec_ref_known(v___x_424_, 1);
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
lean_dec_ref_known(v___x_484_, 1);
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
lean_dec_ref_known(v___x_527_, 1);
lean_inc_ref(v_a_515_);
v___x_528_ = l_Lean_Elab_getFixedParamPerms(v_a_515_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_n(v_a_529_, 2);
lean_dec_ref_known(v___x_528_, 1);
lean_inc_ref(v_a_515_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_529_, v_sz_516_, v___x_517_, v_a_515_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; size_t v_sz_535_; lean_object* v___x_536_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_array_get_size(v_a_515_);
lean_inc_ref(v_a_515_);
v___x_534_ = l_Array_toSubarray___redArg(v_a_515_, v___x_532_, v___x_533_);
v_sz_535_ = lean_array_size(v_a_531_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_531_, v_sz_535_, v___x_517_, v___x_534_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; lean_object* v_numSectionVars_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v___x_536_, 1);
v___x_537_ = lean_array_get_borrowed(v___x_519_, v_a_515_, v___x_532_);
v_numSectionVars_538_ = lean_ctor_get(v___x_537_, 5);
lean_inc(v_numSectionVars_538_);
lean_inc_ref(v_a_515_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_515_, v_numSectionVars_538_, v_sz_516_, v___x_517_, v_a_515_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
lean_inc(v_a_531_);
lean_inc(v_a_529_);
v___x_541_ = l_Lean_Elab_WF_packMutual(v_a_529_, v_a_531_, v_a_540_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
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
lean_ctor_set(v___x_546_, 0, v_a_531_);
lean_ctor_set(v___x_546_, 1, v_a_542_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_529_);
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
lean_dec(v_a_531_);
lean_dec(v_a_529_);
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
lean_dec(v_a_531_);
lean_dec(v_a_529_);
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
lean_dec(v_a_531_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_515_);
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
lean_dec(v_a_529_);
lean_dec_ref(v_a_515_);
v_a_576_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_530_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_530_);
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
lean_dec_ref(v_a_515_);
v_a_584_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_528_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_528_);
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
lean_dec_ref(v_a_515_);
v_a_592_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_527_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_527_);
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
size_t v_sz_boxed_612_; size_t v___x_43728__boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_601_);
lean_dec(v_sz_601_);
v___x_43728__boxed_613_ = lean_unbox_usize(v___x_602_);
lean_dec(v___x_602_);
v_res_614_ = l_Lean_Elab_wfRecursion___lam__0(v_a_600_, v_sz_boxed_612_, v___x_43728__boxed_613_, v___x_603_, v___x_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
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
v_options_626_ = lean_ctor_get(v___y_623_, 1);
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
lean_object* v_toCold_630_; lean_object* v_inheritedTraceOptions_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_toCold_630_ = lean_ctor_get(v___y_623_, 0);
v_inheritedTraceOptions_631_ = lean_ctor_get(v_toCold_630_, 4);
v___x_632_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
v___x_633_ = l_Lean_Name_append(v___x_632_, v___x_618_);
v___x_634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_631_, v_options_626_, v___x_633_);
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
lean_dec_ref_known(v___x_654_, 1);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_715_, uint8_t v___y_716_, lean_object* v_x_717_){
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
return v___x_725_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_727_ = lean_string_dec_eq(v_str_720_, v___x_726_);
if (v___x_727_ == 0)
{
return v___x_727_;
}
else
{
return v_suppressElabErrors_715_;
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
return v___x_729_;
}
else
{
return v_suppressElabErrors_715_;
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
return v___x_735_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_737_ = lean_string_dec_eq(v_str_732_, v___x_736_);
if (v___x_737_ == 0)
{
return v___x_737_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_739_ = lean_string_dec_eq(v_str_731_, v___x_738_);
if (v___x_739_ == 0)
{
return v___x_739_;
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
return v___y_716_;
}
}
default: 
{
return v___y_716_;
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
return v___x_742_;
}
else
{
return v_suppressElabErrors_715_;
}
}
default: 
{
return v___y_716_;
}
}
}
else
{
return v___y_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_743_, lean_object* v___y_744_, lean_object* v_x_745_){
_start:
{
uint8_t v_suppressElabErrors_boxed_746_; uint8_t v___y_44058__boxed_747_; uint8_t v_res_748_; lean_object* v_r_749_; 
v_suppressElabErrors_boxed_746_ = lean_unbox(v_suppressElabErrors_743_);
v___y_44058__boxed_747_ = lean_unbox(v___y_744_);
v_res_748_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_746_, v___y_44058__boxed_747_, v_x_745_);
lean_dec(v_x_745_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_751_, lean_object* v_msgData_752_, uint8_t v_severity_753_, uint8_t v_isSilent_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_797_; uint8_t v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_823_; uint8_t v___y_824_; uint8_t v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_833_; lean_object* v___y_834_; uint8_t v___y_835_; uint8_t v___y_836_; lean_object* v___y_837_; uint8_t v___y_838_; uint8_t v___x_843_; lean_object* v___y_845_; uint8_t v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; uint8_t v___y_849_; uint8_t v___y_850_; uint8_t v___y_852_; uint8_t v___x_866_; 
v___x_843_ = 2;
v___x_866_ = l_Lean_instBEqMessageSeverity_beq(v_severity_753_, v___x_843_);
if (v___x_866_ == 0)
{
v___y_852_ = v___x_866_;
goto v___jp_851_;
}
else
{
uint8_t v___x_867_; 
lean_inc_ref(v_msgData_752_);
v___x_867_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_752_);
v___y_852_ = v___x_867_;
goto v___jp_851_;
}
v___jp_760_:
{
lean_object* v___x_770_; lean_object* v_currNamespace_771_; lean_object* v_openDecls_772_; lean_object* v_env_773_; lean_object* v_nextMacroScope_774_; lean_object* v_ngen_775_; lean_object* v_auxDeclNGen_776_; lean_object* v_traceState_777_; lean_object* v_cache_778_; lean_object* v_messages_779_; lean_object* v_infoState_780_; lean_object* v_snapshotTasks_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_795_; 
v___x_770_ = lean_st_ref_take(v___y_769_);
v_currNamespace_771_ = lean_ctor_get(v___y_768_, 5);
v_openDecls_772_ = lean_ctor_get(v___y_768_, 6);
v_env_773_ = lean_ctor_get(v___x_770_, 0);
v_nextMacroScope_774_ = lean_ctor_get(v___x_770_, 1);
v_ngen_775_ = lean_ctor_get(v___x_770_, 2);
v_auxDeclNGen_776_ = lean_ctor_get(v___x_770_, 3);
v_traceState_777_ = lean_ctor_get(v___x_770_, 4);
v_cache_778_ = lean_ctor_get(v___x_770_, 5);
v_messages_779_ = lean_ctor_get(v___x_770_, 6);
v_infoState_780_ = lean_ctor_get(v___x_770_, 7);
v_snapshotTasks_781_ = lean_ctor_get(v___x_770_, 8);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_795_ == 0)
{
v___x_783_ = v___x_770_;
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
else
{
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
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_inc(v_openDecls_772_);
lean_inc(v_currNamespace_771_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_currNamespace_771_);
lean_ctor_set(v___x_785_, 1, v_openDecls_772_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___y_764_);
lean_inc_ref(v___y_761_);
lean_inc_ref(v___y_767_);
v___x_787_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_787_, 0, v___y_767_);
lean_ctor_set(v___x_787_, 1, v___y_763_);
lean_ctor_set(v___x_787_, 2, v___y_766_);
lean_ctor_set(v___x_787_, 3, v___y_761_);
lean_ctor_set(v___x_787_, 4, v___x_786_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*5, v___y_765_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*5 + 1, v___y_762_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*5 + 2, v_isSilent_754_);
v___x_788_ = l_Lean_MessageLog_add(v___x_787_, v_messages_779_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 6, v___x_788_);
v___x_790_ = v___x_783_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_env_773_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_nextMacroScope_774_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_ngen_775_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_auxDeclNGen_776_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_traceState_777_);
lean_ctor_set(v_reuseFailAlloc_794_, 5, v_cache_778_);
lean_ctor_set(v_reuseFailAlloc_794_, 6, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_794_, 7, v_infoState_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 8, v_snapshotTasks_781_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_st_ref_put(v___y_769_, v___x_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
v___jp_796_:
{
lean_object* v_fileName_804_; lean_object* v_fileMap_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_821_; 
v_fileName_804_ = lean_ctor_get(v___y_802_, 0);
v_fileMap_805_ = lean_ctor_get(v___y_802_, 1);
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
lean_inc_ref_n(v_fileMap_805_, 2);
v___x_812_ = l_Lean_FileMap_toPosition(v_fileMap_805_, v___y_799_);
lean_dec(v___y_799_);
v___x_813_ = l_Lean_FileMap_toPosition(v_fileMap_805_, v___y_803_);
lean_dec(v___y_803_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_800_ == 0)
{
lean_del_object(v___x_810_);
lean_dec_ref(v___y_797_);
v___y_761_ = v___x_815_;
v___y_762_ = v___y_798_;
v___y_763_ = v___x_812_;
v___y_764_ = v_a_808_;
v___y_765_ = v___y_801_;
v___y_766_ = v___x_814_;
v___y_767_ = v_fileName_804_;
v___y_768_ = v___y_757_;
v___y_769_ = v___y_758_;
goto v___jp_760_;
}
else
{
uint8_t v___x_816_; 
lean_inc(v_a_808_);
v___x_816_ = l_Lean_MessageData_hasTag(v___y_797_, v_a_808_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec_ref_known(v___x_814_, 1);
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
v___y_761_ = v___x_815_;
v___y_762_ = v___y_798_;
v___y_763_ = v___x_812_;
v___y_764_ = v_a_808_;
v___y_765_ = v___y_801_;
v___y_766_ = v___x_814_;
v___y_767_ = v_fileName_804_;
v___y_768_ = v___y_757_;
v___y_769_ = v___y_758_;
goto v___jp_760_;
}
}
}
}
v___jp_822_:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Syntax_getTailPos_x3f(v___y_826_, v___y_827_);
lean_dec(v___y_826_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_inc(v___y_829_);
v___y_797_ = v___y_823_;
v___y_798_ = v___y_824_;
v___y_799_ = v___y_829_;
v___y_800_ = v___y_825_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_828_;
v___y_803_ = v___y_829_;
goto v___jp_796_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_830_, 1);
v___y_797_ = v___y_823_;
v___y_798_ = v___y_824_;
v___y_799_ = v___y_829_;
v___y_800_ = v___y_825_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_828_;
v___y_803_ = v_val_831_;
goto v___jp_796_;
}
}
v___jp_832_:
{
lean_object* v_ref_839_; lean_object* v___x_840_; 
v_ref_839_ = l_Lean_replaceRef(v_ref_751_, v___y_834_);
v___x_840_ = l_Lean_Syntax_getPos_x3f(v_ref_839_, v___y_836_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___y_823_ = v___y_833_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_835_;
v___y_826_ = v_ref_839_;
v___y_827_ = v___y_836_;
v___y_828_ = v___y_837_;
v___y_829_ = v___x_841_;
goto v___jp_822_;
}
else
{
lean_object* v_val_842_; 
v_val_842_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v___x_840_, 1);
v___y_823_ = v___y_833_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_835_;
v___y_826_ = v_ref_839_;
v___y_827_ = v___y_836_;
v___y_828_ = v___y_837_;
v___y_829_ = v_val_842_;
goto v___jp_822_;
}
}
v___jp_844_:
{
if (v___y_850_ == 0)
{
v___y_833_ = v___y_847_;
v___y_834_ = v___y_845_;
v___y_835_ = v___y_846_;
v___y_836_ = v___y_849_;
v___y_837_ = v___y_848_;
v___y_838_ = v_severity_753_;
goto v___jp_832_;
}
else
{
v___y_833_ = v___y_847_;
v___y_834_ = v___y_845_;
v___y_835_ = v___y_846_;
v___y_836_ = v___y_849_;
v___y_837_ = v___y_848_;
v___y_838_ = v___x_843_;
goto v___jp_832_;
}
}
v___jp_851_:
{
if (v___y_852_ == 0)
{
lean_object* v_toCold_853_; lean_object* v_options_854_; lean_object* v_ref_855_; uint8_t v_suppressElabErrors_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___f_859_; uint8_t v___x_860_; uint8_t v___x_861_; 
v_toCold_853_ = lean_ctor_get(v___y_757_, 0);
v_options_854_ = lean_ctor_get(v___y_757_, 1);
v_ref_855_ = lean_ctor_get(v___y_757_, 4);
v_suppressElabErrors_856_ = lean_ctor_get_uint8(v___y_757_, sizeof(void*)*10 + 1);
v___x_857_ = lean_box(v_suppressElabErrors_856_);
v___x_858_ = lean_box(v___y_852_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_859_, 0, v___x_857_);
lean_closure_set(v___f_859_, 1, v___x_858_);
v___x_860_ = 1;
v___x_861_ = l_Lean_instBEqMessageSeverity_beq(v_severity_753_, v___x_860_);
if (v___x_861_ == 0)
{
v___y_845_ = v_ref_855_;
v___y_846_ = v_suppressElabErrors_856_;
v___y_847_ = v___f_859_;
v___y_848_ = v_toCold_853_;
v___y_849_ = v___y_852_;
v___y_850_ = v___x_861_;
goto v___jp_844_;
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = l_Lean_warningAsError;
v___x_863_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_854_, v___x_862_);
v___y_845_ = v_ref_855_;
v___y_846_ = v_suppressElabErrors_856_;
v___y_847_ = v___f_859_;
v___y_848_ = v_toCold_853_;
v___y_849_ = v___y_852_;
v___y_850_ = v___x_863_;
goto v___jp_844_;
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref(v_msgData_752_);
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_868_, lean_object* v_msgData_869_, lean_object* v_severity_870_, lean_object* v_isSilent_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v_severity_boxed_877_; uint8_t v_isSilent_boxed_878_; lean_object* v_res_879_; 
v_severity_boxed_877_ = lean_unbox(v_severity_870_);
v_isSilent_boxed_878_ = lean_unbox(v_isSilent_871_);
v_res_879_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_868_, v_msgData_869_, v_severity_boxed_877_, v_isSilent_boxed_878_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v_ref_868_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_880_, lean_object* v_msgData_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; 
v___x_889_ = 1;
v___x_890_ = 0;
v___x_891_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_880_, v_msgData_881_, v___x_889_, v___x_890_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_892_, lean_object* v_msgData_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_892_, v_msgData_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v_ref_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v___x_910_, lean_object* v_as_911_, size_t v_i_912_, size_t v_stop_913_, lean_object* v_b_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_a_923_; uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_eq(v_i_912_, v_stop_913_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v_name_929_; lean_object* v_stx_930_; uint8_t v___y_932_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_928_ = lean_array_uget_borrowed(v_as_911_, v_i_912_);
v_name_929_ = lean_ctor_get(v___x_928_, 0);
v_stx_930_ = lean_ctor_get(v___x_928_, 1);
v___x_942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_943_ = lean_name_eq(v_name_929_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_945_ = lean_name_eq(v_name_929_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_box(0);
v_a_923_ = v___x_946_;
goto v___jp_922_;
}
else
{
v___y_932_ = v___x_945_;
goto v___jp_931_;
}
}
else
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_nat_dec_lt(v___x_947_, v___x_910_);
v___y_932_ = v___x_948_;
goto v___jp_931_;
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_929_);
v___x_934_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_929_, v___y_932_);
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
lean_dec_ref(v___x_934_);
v___x_936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
v___x_938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
v___x_939_ = l_Lean_MessageData_ofFormat(v___x_938_);
v___x_940_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_930_, v___x_939_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v_a_923_ = v_a_941_;
goto v___jp_922_;
}
else
{
return v___x_940_;
}
}
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_914_);
return v___x_949_;
}
v___jp_922_:
{
size_t v___x_924_; size_t v___x_925_; 
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_912_, v___x_924_);
v_i_912_ = v___x_925_;
v_b_914_ = v_a_923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v___x_950_, lean_object* v_as_951_, lean_object* v_i_952_, lean_object* v_stop_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
size_t v_i_boxed_962_; size_t v_stop_boxed_963_; lean_object* v_res_964_; 
v_i_boxed_962_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_stop_boxed_963_ = lean_unbox_usize(v_stop_953_);
lean_dec(v_stop_953_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_950_, v_as_951_, v_i_boxed_962_, v_stop_boxed_963_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
lean_dec(v___x_950_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_965_, lean_object* v_as_966_, size_t v_i_967_, size_t v_stop_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_a_978_; lean_object* v___y_983_; uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_eq(v_i_967_, v_stop_968_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v_modifiers_987_; lean_object* v_attrs_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_986_ = lean_array_uget_borrowed(v_as_966_, v_i_967_);
v_modifiers_987_ = lean_ctor_get(v___x_986_, 2);
v_attrs_988_ = lean_ctor_get(v_modifiers_987_, 2);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_array_get_size(v_attrs_988_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
if (v___x_992_ == 0)
{
v_a_978_ = v___x_991_;
goto v___jp_977_;
}
else
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_le(v___x_990_, v___x_990_);
if (v___x_993_ == 0)
{
if (v___x_992_ == 0)
{
v_a_978_ = v___x_991_;
goto v___jp_977_;
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_of_nat(v___x_990_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_965_, v_attrs_988_, v___x_994_, v___x_995_, v___x_991_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
v___y_983_ = v___x_996_;
goto v___jp_982_;
}
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_990_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_965_, v_attrs_988_, v___x_997_, v___x_998_, v___x_991_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
v___y_983_ = v___x_999_;
goto v___jp_982_;
}
}
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_b_969_);
return v___x_1000_;
}
v___jp_977_:
{
size_t v___x_979_; size_t v___x_980_; 
v___x_979_ = ((size_t)1ULL);
v___x_980_ = lean_usize_add(v_i_967_, v___x_979_);
v_i_967_ = v___x_980_;
v_b_969_ = v_a_978_;
goto _start;
}
v___jp_982_:
{
if (lean_obj_tag(v___y_983_) == 0)
{
lean_object* v_a_984_; 
v_a_984_ = lean_ctor_get(v___y_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___y_983_, 1);
v_a_978_ = v_a_984_;
goto v___jp_977_;
}
else
{
return v___y_983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_1001_, lean_object* v_as_1002_, lean_object* v_i_1003_, lean_object* v_stop_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
size_t v_i_boxed_1013_; size_t v_stop_boxed_1014_; lean_object* v_res_1015_; 
v_i_boxed_1013_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_stop_boxed_1014_ = lean_unbox_usize(v_stop_1004_);
lean_dec(v_stop_1004_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1001_, v_as_1002_, v_i_boxed_1013_, v_stop_boxed_1014_, v_b_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_as_1002_);
lean_dec(v___x_1001_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1016_, size_t v_i_1017_, lean_object* v_bs_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_lt(v_i_1017_, v_sz_1016_);
if (v___x_1019_ == 0)
{
return v_bs_1018_;
}
else
{
lean_object* v_v_1020_; lean_object* v_termination_1021_; lean_object* v_decreasingBy_x3f_1022_; lean_object* v___x_1023_; lean_object* v_bs_x27_1024_; size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v_v_1020_ = lean_array_uget_borrowed(v_bs_1018_, v_i_1017_);
v_termination_1021_ = lean_ctor_get(v_v_1020_, 8);
v_decreasingBy_x3f_1022_ = lean_ctor_get(v_termination_1021_, 4);
lean_inc(v_decreasingBy_x3f_1022_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v_bs_x27_1024_ = lean_array_uset(v_bs_1018_, v_i_1017_, v___x_1023_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_1017_, v___x_1025_);
v___x_1027_ = lean_array_uset(v_bs_x27_1024_, v_i_1017_, v_decreasingBy_x3f_1022_);
v_i_1017_ = v___x_1026_;
v_bs_1018_ = v___x_1027_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1029_, lean_object* v_i_1030_, lean_object* v_bs_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1029_);
lean_dec(v_sz_1029_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1032_, v_i_boxed_1033_, v_bs_1031_);
return v_res_1034_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1035_; double v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_float_of_nat(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_ref_1046_; lean_object* v___x_1047_; lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1092_; 
v_ref_1046_ = lean_ctor_get(v___y_1043_, 4);
v___x_1047_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1092_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1092_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v_traceState_1053_; lean_object* v_env_1054_; lean_object* v_nextMacroScope_1055_; lean_object* v_ngen_1056_; lean_object* v_auxDeclNGen_1057_; lean_object* v_cache_1058_; lean_object* v_messages_1059_; lean_object* v_infoState_1060_; lean_object* v_snapshotTasks_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1091_; 
v___x_1052_ = lean_st_ref_take(v___y_1044_);
v_traceState_1053_ = lean_ctor_get(v___x_1052_, 4);
v_env_1054_ = lean_ctor_get(v___x_1052_, 0);
v_nextMacroScope_1055_ = lean_ctor_get(v___x_1052_, 1);
v_ngen_1056_ = lean_ctor_get(v___x_1052_, 2);
v_auxDeclNGen_1057_ = lean_ctor_get(v___x_1052_, 3);
v_cache_1058_ = lean_ctor_get(v___x_1052_, 5);
v_messages_1059_ = lean_ctor_get(v___x_1052_, 6);
v_infoState_1060_ = lean_ctor_get(v___x_1052_, 7);
v_snapshotTasks_1061_ = lean_ctor_get(v___x_1052_, 8);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1091_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snapshotTasks_1061_);
lean_inc(v_infoState_1060_);
lean_inc(v_messages_1059_);
lean_inc(v_cache_1058_);
lean_inc(v_traceState_1053_);
lean_inc(v_auxDeclNGen_1057_);
lean_inc(v_ngen_1056_);
lean_inc(v_nextMacroScope_1055_);
lean_inc(v_env_1054_);
lean_dec(v___x_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1091_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
uint64_t v_tid_1065_; lean_object* v_traces_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1090_; 
v_tid_1065_ = lean_ctor_get_uint64(v_traceState_1053_, sizeof(void*)*1);
v_traces_1066_ = lean_ctor_get(v_traceState_1053_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_traceState_1053_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1068_ = v_traceState_1053_;
v_isShared_1069_ = v_isSharedCheck_1090_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_traces_1066_);
lean_dec(v_traceState_1053_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1090_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; double v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1072_ = 0;
v___x_1073_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1074_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1074_, 0, v_cls_1039_);
lean_ctor_set(v___x_1074_, 1, v___x_1070_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
lean_ctor_set_float(v___x_1074_, sizeof(void*)*3, v___x_1071_);
lean_ctor_set_float(v___x_1074_, sizeof(void*)*3 + 8, v___x_1071_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*3 + 16, v___x_1072_);
v___x_1075_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1076_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v_a_1048_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
lean_inc(v_ref_1046_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_ref_1046_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_PersistentArray_push___redArg(v_traces_1066_, v___x_1077_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1078_);
v___x_1080_ = v___x_1068_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1078_);
lean_ctor_set_uint64(v_reuseFailAlloc_1089_, sizeof(void*)*1, v_tid_1065_);
v___x_1080_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 4, v___x_1080_);
v___x_1082_ = v___x_1063_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_env_1054_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_nextMacroScope_1055_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_ngen_1056_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_auxDeclNGen_1057_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1088_, 5, v_cache_1058_);
lean_ctor_set(v_reuseFailAlloc_1088_, 6, v_messages_1059_);
lean_ctor_set(v_reuseFailAlloc_1088_, 7, v_infoState_1060_);
lean_ctor_set(v_reuseFailAlloc_1088_, 8, v_snapshotTasks_1061_);
v___x_1082_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = lean_st_ref_put(v___y_1044_, v___x_1082_);
v___x_1084_ = lean_box(0);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1084_);
v___x_1086_ = v___x_1050_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1093_, lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1093_, v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1100_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1104_, lean_object* v_snd_1105_, size_t v_sz_1106_, size_t v___x_1107_, lean_object* v_a_1108_, lean_object* v_fixedArgs_1109_, lean_object* v_fst_1110_, lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v___x_1113_, lean_object* v_wfRel_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v_a_1130_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_options_1279_; uint8_t v_hasTrace_1280_; 
v_options_1279_ = lean_ctor_get(v___y_1119_, 1);
v_hasTrace_1280_ = lean_ctor_get_uint8(v_options_1279_, sizeof(void*)*1);
if (v_hasTrace_1280_ == 0)
{
lean_dec(v___x_1113_);
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
v___y_1257_ = v___y_1117_;
v___y_1258_ = v___y_1118_;
v___y_1259_ = v___y_1119_;
v___y_1260_ = v___y_1120_;
goto v___jp_1254_;
}
else
{
lean_object* v_toCold_1281_; lean_object* v_inheritedTraceOptions_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_toCold_1281_ = lean_ctor_get(v___y_1119_, 0);
v_inheritedTraceOptions_1282_ = lean_ctor_get(v_toCold_1281_, 4);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
lean_inc(v___x_1113_);
v___x_1284_ = l_Lean_Name_append(v___x_1283_, v___x_1113_);
v___x_1285_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1282_, v_options_1279_, v___x_1284_);
lean_dec(v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v___x_1113_);
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
v___y_1257_ = v___y_1117_;
v___y_1258_ = v___y_1118_;
v___y_1259_ = v___y_1119_;
v___y_1260_ = v___y_1120_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1114_);
v___x_1287_ = l_Lean_MessageData_ofExpr(v_wfRel_1114_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1113_, v___x_1288_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
v___y_1257_ = v___y_1117_;
v___y_1258_ = v___y_1118_;
v___y_1259_ = v___y_1119_;
v___y_1260_ = v___y_1120_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_wfRel_1114_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_fst_1110_);
lean_dec_ref(v_fixedArgs_1109_);
lean_dec_ref(v_a_1108_);
lean_dec_ref(v_fst_1104_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
v___jp_1122_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v___x_1131_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1129_, v___y_1125_, v___y_1124_);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1131_, 0);
lean_dec(v_unused_1139_);
v___x_1133_ = v___x_1131_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_dec(v___x_1131_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 0, v_a_1130_);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
v___jp_1140_:
{
if (lean_obj_tag(v___y_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_env_1152_; lean_object* v___x_1153_; 
v_a_1149_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___y_1148_, 1);
v___x_1150_ = lean_st_ref_get(v___y_1142_);
v___x_1151_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1147_, v___y_1143_, v___y_1142_);
lean_dec_ref(v___x_1151_);
v_env_1152_ = lean_ctor_get(v___x_1150_, 0);
lean_inc_ref_n(v_env_1152_, 2);
lean_dec(v___x_1150_);
v___x_1153_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1152_, v_a_1149_, v___y_1144_, v___y_1142_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1213_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1213_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1213_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v_env_1159_; lean_object* v_nextMacroScope_1160_; lean_object* v_ngen_1161_; lean_object* v_auxDeclNGen_1162_; lean_object* v_traceState_1163_; lean_object* v_messages_1164_; lean_object* v_infoState_1165_; lean_object* v_snapshotTasks_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1211_; 
v___x_1158_ = lean_st_ref_take(v___y_1142_);
v_env_1159_ = lean_ctor_get(v___x_1158_, 0);
v_nextMacroScope_1160_ = lean_ctor_get(v___x_1158_, 1);
v_ngen_1161_ = lean_ctor_get(v___x_1158_, 2);
v_auxDeclNGen_1162_ = lean_ctor_get(v___x_1158_, 3);
v_traceState_1163_ = lean_ctor_get(v___x_1158_, 4);
v_messages_1164_ = lean_ctor_get(v___x_1158_, 6);
v_infoState_1165_ = lean_ctor_get(v___x_1158_, 7);
v_snapshotTasks_1166_ = lean_ctor_get(v___x_1158_, 8);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1158_, 5);
lean_dec(v_unused_1212_);
v___x_1168_ = v___x_1158_;
v_isShared_1169_ = v_isSharedCheck_1211_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snapshotTasks_1166_);
lean_inc(v_infoState_1165_);
lean_inc(v_messages_1164_);
lean_inc(v_traceState_1163_);
lean_inc(v_auxDeclNGen_1162_);
lean_inc(v_ngen_1161_);
lean_inc(v_nextMacroScope_1160_);
lean_inc(v_env_1159_);
lean_dec(v___x_1158_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1211_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = l_Lean_copyExtraModUses(v_env_1152_, v_env_1159_);
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
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_nextMacroScope_1160_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_ngen_1161_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_auxDeclNGen_1162_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_traceState_1163_);
lean_ctor_set(v_reuseFailAlloc_1210_, 5, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1210_, 6, v_messages_1164_);
lean_ctor_set(v_reuseFailAlloc_1210_, 7, v_infoState_1165_);
lean_ctor_set(v_reuseFailAlloc_1210_, 8, v_snapshotTasks_1166_);
v___x_1173_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_mctx_1176_; lean_object* v_zetaDeltaFVarIds_1177_; lean_object* v_postponed_1178_; lean_object* v_diag_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1208_; 
v___x_1174_ = lean_st_ref_put(v___y_1142_, v___x_1173_);
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
v___x_1186_ = lean_st_ref_put(v___y_1143_, v___x_1185_);
v_ref_1187_ = lean_ctor_get(v_fst_1104_, 0);
v_kind_1188_ = lean_ctor_get_uint8(v_fst_1104_, sizeof(void*)*9);
v_levelParams_1189_ = lean_ctor_get(v_fst_1104_, 1);
v_modifiers_1190_ = lean_ctor_get(v_fst_1104_, 2);
v_declName_1191_ = lean_ctor_get(v_fst_1104_, 3);
v_binders_1192_ = lean_ctor_get(v_fst_1104_, 4);
v_numSectionVars_1193_ = lean_ctor_get(v_fst_1104_, 5);
v_type_1194_ = lean_ctor_get(v_fst_1104_, 6);
v_termination_1195_ = lean_ctor_get(v_fst_1104_, 8);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_fst_1104_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_fst_1104_, 7);
lean_dec(v_unused_1206_);
v___x_1197_ = v_fst_1104_;
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
lean_dec(v_fst_1104_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 7, v_a_1154_);
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
lean_ctor_set(v_reuseFailAlloc_1204_, 7, v_a_1154_);
lean_ctor_set(v_reuseFailAlloc_1204_, 8, v_termination_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*9, v_kind_1188_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1200_);
v___x_1202_ = v___x_1156_;
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
lean_dec_ref(v_env_1152_);
lean_dec_ref(v_fst_1104_);
v_a_1214_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1153_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1153_);
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
lean_dec_ref(v_fst_1104_);
v_a_1222_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___y_1148_, 1);
v___y_1123_ = v___y_1141_;
v___y_1124_ = v___y_1142_;
v___y_1125_ = v___y_1143_;
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1145_;
v___y_1128_ = v___y_1146_;
v___y_1129_ = v___y_1147_;
v_a_1130_ = v_a_1222_;
goto v___jp_1122_;
}
}
v___jp_1223_:
{
lean_object* v___x_1230_; lean_object* v_env_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_st_ref_get(v___y_1229_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1105_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref_known(v___x_1232_, 1);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1106_, v___x_1107_, v_a_1108_);
lean_inc_ref(v_fst_1104_);
v___x_1234_ = l_Lean_Elab_WF_mkFix(v_fst_1104_, v_fixedArgs_1109_, v_fst_1110_, v_wfRel_1114_, v___x_1111_, v___x_1233_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1235_, v___y_1228_, v___y_1229_);
v___y_1141_ = v___y_1225_;
v___y_1142_ = v___y_1229_;
v___y_1143_ = v___y_1227_;
v___y_1144_ = v___y_1228_;
v___y_1145_ = v___y_1224_;
v___y_1146_ = v___y_1226_;
v___y_1147_ = v_env_1231_;
v___y_1148_ = v___x_1236_;
goto v___jp_1140_;
}
else
{
v___y_1141_ = v___y_1225_;
v___y_1142_ = v___y_1229_;
v___y_1143_ = v___y_1227_;
v___y_1144_ = v___y_1228_;
v___y_1145_ = v___y_1224_;
v___y_1146_ = v___y_1226_;
v___y_1147_ = v_env_1231_;
v___y_1148_ = v___x_1234_;
goto v___jp_1140_;
}
}
else
{
lean_object* v_a_1237_; 
lean_dec_ref(v_wfRel_1114_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_fst_1110_);
lean_dec_ref(v_fixedArgs_1109_);
lean_dec_ref(v_a_1108_);
lean_dec_ref(v_fst_1104_);
v_a_1237_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1232_, 1);
v___y_1123_ = v___y_1225_;
v___y_1124_ = v___y_1229_;
v___y_1125_ = v___y_1227_;
v___y_1126_ = v___y_1228_;
v___y_1127_ = v___y_1224_;
v___y_1128_ = v___y_1226_;
v___y_1129_ = v_env_1231_;
v_a_1130_ = v_a_1237_;
goto v___jp_1122_;
}
}
v___jp_1238_:
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_dec_ref_known(v___y_1245_, 1);
v___y_1224_ = v___y_1239_;
v___y_1225_ = v___y_1241_;
v___y_1226_ = v___y_1243_;
v___y_1227_ = v___y_1240_;
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1242_;
goto v___jp_1223_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_wfRel_1114_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_fst_1110_);
lean_dec_ref(v_fixedArgs_1109_);
lean_dec_ref(v_a_1108_);
lean_dec_ref(v_fst_1104_);
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
lean_inc_ref(v_wfRel_1114_);
v___x_1261_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1114_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_array_get_size(v_a_1108_);
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
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1264_, v_a_1108_, v___x_1107_, v___x_1267_, v___x_1112_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
v___y_1239_ = v___y_1255_;
v___y_1240_ = v___y_1258_;
v___y_1241_ = v___y_1256_;
v___y_1242_ = v___y_1260_;
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___x_1268_;
goto v___jp_1238_;
}
}
else
{
size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_usize_of_nat(v___x_1264_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1264_, v_a_1108_, v___x_1107_, v___x_1269_, v___x_1112_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
v___y_1239_ = v___y_1255_;
v___y_1240_ = v___y_1258_;
v___y_1241_ = v___y_1256_;
v___y_1242_ = v___y_1260_;
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___x_1270_;
goto v___jp_1238_;
}
}
}
else
{
lean_dec_ref_known(v_a_1262_, 1);
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
lean_dec_ref(v_wfRel_1114_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_fst_1110_);
lean_dec_ref(v_fixedArgs_1109_);
lean_dec_ref(v_a_1108_);
lean_dec_ref(v_fst_1104_);
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
lean_object* v_fst_1298_ = _args[0];
lean_object* v_snd_1299_ = _args[1];
lean_object* v_sz_1300_ = _args[2];
lean_object* v___x_1301_ = _args[3];
lean_object* v_a_1302_ = _args[4];
lean_object* v_fixedArgs_1303_ = _args[5];
lean_object* v_fst_1304_ = _args[6];
lean_object* v___x_1305_ = _args[7];
lean_object* v___x_1306_ = _args[8];
lean_object* v___x_1307_ = _args[9];
lean_object* v_wfRel_1308_ = _args[10];
lean_object* v___y_1309_ = _args[11];
lean_object* v___y_1310_ = _args[12];
lean_object* v___y_1311_ = _args[13];
lean_object* v___y_1312_ = _args[14];
lean_object* v___y_1313_ = _args[15];
lean_object* v___y_1314_ = _args[16];
lean_object* v___y_1315_ = _args[17];
_start:
{
size_t v_sz_boxed_1316_; size_t v___x_44659__boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v___x_44659__boxed_1317_ = lean_unbox_usize(v___x_1301_);
lean_dec(v___x_1301_);
v_res_1318_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1298_, v_snd_1299_, v_sz_boxed_1316_, v___x_44659__boxed_1317_, v_a_1302_, v_fixedArgs_1303_, v_fst_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v_wfRel_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_snd_1299_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1322_, size_t v___x_1323_, lean_object* v_a_1324_, lean_object* v_fst_1325_, lean_object* v_snd_1326_, lean_object* v_fst_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v_declName_1330_, lean_object* v_fst_1331_, lean_object* v_wf_1332_, lean_object* v_fixedArgs_1333_, lean_object* v_type_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_whnfForall(v_type_1334_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___x_1357_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1357_ = l_Lean_Expr_isForall(v_a_1343_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_fixedArgs_1333_);
lean_dec_ref(v_wf_1332_);
lean_dec_ref(v_fst_1331_);
lean_dec(v_declName_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v_fst_1327_);
lean_dec_ref(v_snd_1326_);
lean_dec_ref(v_fst_1325_);
lean_dec_ref(v_a_1324_);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1359_ = l_Lean_MessageData_ofExpr(v_a_1343_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1360_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
v___y_1345_ = v___y_1335_;
v___y_1346_ = v___y_1336_;
v___y_1347_ = v___y_1337_;
v___y_1348_ = v___y_1338_;
v___y_1349_ = v___y_1339_;
v___y_1350_ = v___y_1340_;
goto v___jp_1344_;
}
v___jp_1344_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; 
v___x_1351_ = l_Lean_Expr_bindingDomain_x21(v_a_1343_);
lean_dec(v_a_1343_);
lean_inc_ref(v_a_1324_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_1322_, v___x_1323_, v_a_1324_);
v___x_1353_ = lean_box_usize(v_sz_1322_);
v___x_1354_ = lean_box_usize(v___x_1323_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v_fst_1327_);
lean_inc_ref(v_fixedArgs_1333_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1355_, 0, v_fst_1325_);
lean_closure_set(v___f_1355_, 1, v_snd_1326_);
lean_closure_set(v___f_1355_, 2, v___x_1353_);
lean_closure_set(v___f_1355_, 3, v___x_1354_);
lean_closure_set(v___f_1355_, 4, v_a_1324_);
lean_closure_set(v___f_1355_, 5, v_fixedArgs_1333_);
lean_closure_set(v___f_1355_, 6, v_fst_1327_);
lean_closure_set(v___f_1355_, 7, v___x_1352_);
lean_closure_set(v___f_1355_, 8, v___x_1328_);
lean_closure_set(v___f_1355_, 9, v___x_1329_);
v___x_1356_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1352_, v_declName_1330_, v_fst_1331_, v_fixedArgs_1333_, v_fst_1327_, v___x_1351_, v_wf_1332_, v___f_1355_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1356_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_fixedArgs_1333_);
lean_dec_ref(v_wf_1332_);
lean_dec_ref(v_fst_1331_);
lean_dec(v_declName_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v_fst_1327_);
lean_dec_ref(v_snd_1326_);
lean_dec_ref(v_fst_1325_);
lean_dec_ref(v_a_1324_);
v_a_1370_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1342_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1342_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1378_ = _args[0];
lean_object* v___x_1379_ = _args[1];
lean_object* v_a_1380_ = _args[2];
lean_object* v_fst_1381_ = _args[3];
lean_object* v_snd_1382_ = _args[4];
lean_object* v_fst_1383_ = _args[5];
lean_object* v___x_1384_ = _args[6];
lean_object* v___x_1385_ = _args[7];
lean_object* v_declName_1386_ = _args[8];
lean_object* v_fst_1387_ = _args[9];
lean_object* v_wf_1388_ = _args[10];
lean_object* v_fixedArgs_1389_ = _args[11];
lean_object* v_type_1390_ = _args[12];
lean_object* v___y_1391_ = _args[13];
lean_object* v___y_1392_ = _args[14];
lean_object* v___y_1393_ = _args[15];
lean_object* v___y_1394_ = _args[16];
lean_object* v___y_1395_ = _args[17];
lean_object* v___y_1396_ = _args[18];
lean_object* v___y_1397_ = _args[19];
_start:
{
size_t v_sz_boxed_1398_; size_t v___x_45017__boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v___x_45017__boxed_1399_ = lean_unbox_usize(v___x_1379_);
lean_dec(v___x_1379_);
v_res_1400_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1398_, v___x_45017__boxed_1399_, v_a_1380_, v_fst_1381_, v_snd_1382_, v_fst_1383_, v___x_1384_, v___x_1385_, v_declName_1386_, v_fst_1387_, v_wf_1388_, v_fixedArgs_1389_, v_type_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1401_, lean_object* v_fst_1402_, lean_object* v_fst_1403_, lean_object* v_fst_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Elab_WF_guessLex(v_a_1401_, v_fst_1402_, v_fst_1403_, v_fst_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1413_, lean_object* v_fst_1414_, lean_object* v_fst_1415_, lean_object* v_fst_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1413_, v_fst_1414_, v_fst_1415_, v_fst_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1425_, uint8_t v_isExporting_1426_, lean_object* v___x_1427_, lean_object* v___y_1428_, lean_object* v___x_1429_, lean_object* v_a_x3f_1430_){
_start:
{
lean_object* v___x_1432_; lean_object* v_env_1433_; lean_object* v_nextMacroScope_1434_; lean_object* v_ngen_1435_; lean_object* v_auxDeclNGen_1436_; lean_object* v_traceState_1437_; lean_object* v_messages_1438_; lean_object* v_infoState_1439_; lean_object* v_snapshotTasks_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1465_; 
v___x_1432_ = lean_st_ref_take(v___y_1425_);
v_env_1433_ = lean_ctor_get(v___x_1432_, 0);
v_nextMacroScope_1434_ = lean_ctor_get(v___x_1432_, 1);
v_ngen_1435_ = lean_ctor_get(v___x_1432_, 2);
v_auxDeclNGen_1436_ = lean_ctor_get(v___x_1432_, 3);
v_traceState_1437_ = lean_ctor_get(v___x_1432_, 4);
v_messages_1438_ = lean_ctor_get(v___x_1432_, 6);
v_infoState_1439_ = lean_ctor_get(v___x_1432_, 7);
v_snapshotTasks_1440_ = lean_ctor_get(v___x_1432_, 8);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1432_, 5);
lean_dec(v_unused_1466_);
v___x_1442_ = v___x_1432_;
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snapshotTasks_1440_);
lean_inc(v_infoState_1439_);
lean_inc(v_messages_1438_);
lean_inc(v_traceState_1437_);
lean_inc(v_auxDeclNGen_1436_);
lean_inc(v_ngen_1435_);
lean_inc(v_nextMacroScope_1434_);
lean_inc(v_env_1433_);
lean_dec(v___x_1432_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = l_Lean_Environment_setExporting(v_env_1433_, v_isExporting_1426_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 5, v___x_1427_);
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_nextMacroScope_1434_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_ngen_1435_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_auxDeclNGen_1436_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_traceState_1437_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_messages_1438_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_infoState_1439_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_snapshotTasks_1440_);
v___x_1446_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_mctx_1449_; lean_object* v_zetaDeltaFVarIds_1450_; lean_object* v_postponed_1451_; lean_object* v_diag_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v___x_1447_ = lean_st_ref_put(v___y_1425_, v___x_1446_);
v___x_1448_ = lean_st_ref_take(v___y_1428_);
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
lean_ctor_set(v___x_1454_, 1, v___x_1429_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_mctx_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_zetaDeltaFVarIds_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_postponed_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_diag_1452_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_st_ref_put(v___y_1428_, v___x_1457_);
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
lean_object* v___x_1485_; lean_object* v_env_1486_; lean_object* v___x_1487_; uint8_t v_isModule_1488_; 
v___x_1485_ = lean_st_ref_get(v___y_1483_);
v_env_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_env_1486_);
lean_dec(v___x_1485_);
v___x_1487_ = l_Lean_Environment_header(v_env_1486_);
v_isModule_1488_ = lean_ctor_get_uint8(v___x_1487_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1487_);
if (v_isModule_1488_ == 0)
{
lean_object* v___x_1489_; 
lean_dec_ref(v_env_1486_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v___x_1489_ = lean_apply_7(v_x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1489_;
}
else
{
uint8_t v_isExporting_1490_; 
v_isExporting_1490_ = lean_ctor_get_uint8(v_env_1486_, sizeof(void*)*8);
lean_dec_ref(v_env_1486_);
if (v_isExporting_1477_ == 0)
{
if (v_isExporting_1490_ == 0)
{
lean_object* v___x_1556_; 
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v___x_1556_ = lean_apply_7(v_x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1556_;
}
else
{
goto v___jp_1491_;
}
}
else
{
if (v_isExporting_1490_ == 0)
{
goto v___jp_1491_;
}
else
{
lean_object* v___x_1557_; 
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v___x_1557_ = lean_apply_7(v_x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1557_;
}
}
v___jp_1491_:
{
lean_object* v___x_1492_; lean_object* v_env_1493_; lean_object* v_nextMacroScope_1494_; lean_object* v_ngen_1495_; lean_object* v_auxDeclNGen_1496_; lean_object* v_traceState_1497_; lean_object* v_messages_1498_; lean_object* v_infoState_1499_; lean_object* v_snapshotTasks_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1554_; 
v___x_1492_ = lean_st_ref_take(v___y_1483_);
v_env_1493_ = lean_ctor_get(v___x_1492_, 0);
v_nextMacroScope_1494_ = lean_ctor_get(v___x_1492_, 1);
v_ngen_1495_ = lean_ctor_get(v___x_1492_, 2);
v_auxDeclNGen_1496_ = lean_ctor_get(v___x_1492_, 3);
v_traceState_1497_ = lean_ctor_get(v___x_1492_, 4);
v_messages_1498_ = lean_ctor_get(v___x_1492_, 6);
v_infoState_1499_ = lean_ctor_get(v___x_1492_, 7);
v_snapshotTasks_1500_ = lean_ctor_get(v___x_1492_, 8);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1492_, 5);
lean_dec(v_unused_1555_);
v___x_1502_ = v___x_1492_;
v_isShared_1503_ = v_isSharedCheck_1554_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_snapshotTasks_1500_);
lean_inc(v_infoState_1499_);
lean_inc(v_messages_1498_);
lean_inc(v_traceState_1497_);
lean_inc(v_auxDeclNGen_1496_);
lean_inc(v_ngen_1495_);
lean_inc(v_nextMacroScope_1494_);
lean_inc(v_env_1493_);
lean_dec(v___x_1492_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1554_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1504_ = l_Lean_Environment_setExporting(v_env_1493_, v_isExporting_1477_);
v___x_1505_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 5, v___x_1505_);
lean_ctor_set(v___x_1502_, 0, v___x_1504_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_nextMacroScope_1494_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_ngen_1495_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_auxDeclNGen_1496_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_traceState_1497_);
lean_ctor_set(v_reuseFailAlloc_1553_, 5, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_messages_1498_);
lean_ctor_set(v_reuseFailAlloc_1553_, 7, v_infoState_1499_);
lean_ctor_set(v_reuseFailAlloc_1553_, 8, v_snapshotTasks_1500_);
v___x_1507_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_mctx_1510_; lean_object* v_zetaDeltaFVarIds_1511_; lean_object* v_postponed_1512_; lean_object* v_diag_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1551_; 
v___x_1508_ = lean_st_ref_put(v___y_1483_, v___x_1507_);
v___x_1509_ = lean_st_ref_take(v___y_1481_);
v_mctx_1510_ = lean_ctor_get(v___x_1509_, 0);
v_zetaDeltaFVarIds_1511_ = lean_ctor_get(v___x_1509_, 2);
v_postponed_1512_ = lean_ctor_get(v___x_1509_, 3);
v_diag_1513_ = lean_ctor_get(v___x_1509_, 4);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v___x_1509_, 1);
lean_dec(v_unused_1552_);
v___x_1515_ = v___x_1509_;
v_isShared_1516_ = v_isSharedCheck_1551_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_diag_1513_);
lean_inc(v_postponed_1512_);
lean_inc(v_zetaDeltaFVarIds_1511_);
lean_inc(v_mctx_1510_);
lean_dec(v___x_1509_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1551_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_mctx_1510_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_zetaDeltaFVarIds_1511_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_postponed_1512_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_diag_1513_);
v___x_1519_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v_r_1521_; 
v___x_1520_ = lean_st_ref_put(v___y_1481_, v___x_1519_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v_r_1521_ = lean_apply_7(v_x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
if (lean_obj_tag(v_r_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1538_; 
v_a_1522_ = lean_ctor_get(v_r_1521_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_r_1521_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1524_ = v_r_1521_;
v_isShared_1525_ = v_isSharedCheck_1538_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v_r_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1538_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
lean_inc(v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 1);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v___x_1528_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1483_, v_isExporting_1490_, v___x_1505_, v___y_1481_, v___x_1517_, v___x_1527_);
lean_dec_ref(v___x_1527_);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1528_, 0);
lean_dec(v_unused_1536_);
v___x_1530_ = v___x_1528_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v___x_1528_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_a_1522_);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1522_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1539_ = lean_ctor_get(v_r_1521_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v_r_1521_, 1);
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1483_, v_isExporting_1490_, v___x_1505_, v___y_1481_, v___x_1517_, v___x_1540_);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v___x_1541_, 0);
lean_dec(v_unused_1549_);
v___x_1543_ = v___x_1541_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v___x_1541_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v_a_1539_);
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1539_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1558_, lean_object* v_isExporting_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v_isExporting_boxed_1567_; lean_object* v_res_1568_; 
v_isExporting_boxed_1567_ = lean_unbox(v_isExporting_1559_);
v_res_1568_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1558_, v_isExporting_boxed_1567_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1569_, uint8_t v_when_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
if (v_when_1570_ == 0)
{
lean_object* v___x_1578_; 
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
v___x_1578_ = lean_apply_7(v_x_1569_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, lean_box(0));
return v___x_1578_;
}
else
{
uint8_t v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = 0;
v___x_1580_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1569_, v___x_1579_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1581_, lean_object* v_when_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v_when_boxed_1590_; lean_object* v_res_1591_; 
v_when_boxed_1590_ = lean_unbox(v_when_1582_);
v_res_1591_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1581_, v_when_boxed_1590_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t v_sz_1592_, size_t v_i_1593_, lean_object* v_bs_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_lt(v_i_1593_, v_sz_1592_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_bs_1594_);
return v___x_1599_;
}
else
{
lean_object* v_v_1600_; lean_object* v_ref_1601_; uint8_t v_kind_1602_; lean_object* v_levelParams_1603_; lean_object* v_modifiers_1604_; lean_object* v_declName_1605_; lean_object* v_binders_1606_; lean_object* v_numSectionVars_1607_; lean_object* v_type_1608_; lean_object* v_value_1609_; lean_object* v_termination_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1633_; 
v_v_1600_ = lean_array_uget(v_bs_1594_, v_i_1593_);
v_ref_1601_ = lean_ctor_get(v_v_1600_, 0);
v_kind_1602_ = lean_ctor_get_uint8(v_v_1600_, sizeof(void*)*9);
v_levelParams_1603_ = lean_ctor_get(v_v_1600_, 1);
v_modifiers_1604_ = lean_ctor_get(v_v_1600_, 2);
v_declName_1605_ = lean_ctor_get(v_v_1600_, 3);
v_binders_1606_ = lean_ctor_get(v_v_1600_, 4);
v_numSectionVars_1607_ = lean_ctor_get(v_v_1600_, 5);
v_type_1608_ = lean_ctor_get(v_v_1600_, 6);
v_value_1609_ = lean_ctor_get(v_v_1600_, 7);
v_termination_1610_ = lean_ctor_get(v_v_1600_, 8);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_v_1600_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1612_ = v_v_1600_;
v_isShared_1613_ = v_isSharedCheck_1633_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_termination_1610_);
lean_inc(v_value_1609_);
lean_inc(v_type_1608_);
lean_inc(v_numSectionVars_1607_);
lean_inc(v_binders_1606_);
lean_inc(v_declName_1605_);
lean_inc(v_modifiers_1604_);
lean_inc(v_levelParams_1603_);
lean_inc(v_ref_1601_);
lean_dec(v_v_1600_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1633_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Elab_WF_floatRecApp(v_value_1609_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v_bs_x27_1617_; lean_object* v___x_1619_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = lean_unsigned_to_nat(0u);
v_bs_x27_1617_ = lean_array_uset(v_bs_1594_, v_i_1593_, v___x_1616_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 7, v_a_1615_);
v___x_1619_ = v___x_1612_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_ref_1601_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_levelParams_1603_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_modifiers_1604_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_declName_1605_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_binders_1606_);
lean_ctor_set(v_reuseFailAlloc_1624_, 5, v_numSectionVars_1607_);
lean_ctor_set(v_reuseFailAlloc_1624_, 6, v_type_1608_);
lean_ctor_set(v_reuseFailAlloc_1624_, 7, v_a_1615_);
lean_ctor_set(v_reuseFailAlloc_1624_, 8, v_termination_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, sizeof(void*)*9, v_kind_1602_);
v___x_1619_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_i_1593_, v___x_1620_);
v___x_1622_ = lean_array_uset(v_bs_x27_1617_, v_i_1593_, v___x_1619_);
v_i_1593_ = v___x_1621_;
v_bs_1594_ = v___x_1622_;
goto _start;
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_del_object(v___x_1612_);
lean_dec_ref(v_termination_1610_);
lean_dec_ref(v_type_1608_);
lean_dec(v_numSectionVars_1607_);
lean_dec(v_binders_1606_);
lean_dec(v_declName_1605_);
lean_dec_ref(v_modifiers_1604_);
lean_dec(v_levelParams_1603_);
lean_dec(v_ref_1601_);
lean_dec_ref(v_bs_1594_);
v_a_1625_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1614_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1614_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* v_sz_1634_, lean_object* v_i_1635_, lean_object* v_bs_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1634_);
lean_dec(v_sz_1634_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_1640_, v_i_boxed_1641_, v_bs_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_bs_1645_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_usize_dec_lt(v_i_1644_, v_sz_1643_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_bs_1645_);
return v___x_1647_;
}
else
{
lean_object* v_v_1648_; 
v_v_1648_ = lean_array_uget_borrowed(v_bs_1645_, v_i_1644_);
if (lean_obj_tag(v_v_1648_) == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref(v_bs_1645_);
v___x_1649_ = lean_box(0);
return v___x_1649_;
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1651_; lean_object* v_bs_x27_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v_val_1650_ = lean_ctor_get(v_v_1648_, 0);
lean_inc(v_val_1650_);
v___x_1651_ = lean_unsigned_to_nat(0u);
v_bs_x27_1652_ = lean_array_uset(v_bs_1645_, v_i_1644_, v___x_1651_);
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_add(v_i_1644_, v___x_1653_);
v___x_1655_ = lean_array_uset(v_bs_x27_1652_, v_i_1644_, v_val_1650_);
v_i_1644_ = v___x_1654_;
v_bs_1645_ = v___x_1655_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_sz_1657_, lean_object* v_i_1658_, lean_object* v_bs_1659_){
_start:
{
size_t v_sz_boxed_1660_; size_t v_i_boxed_1661_; lean_object* v_res_1662_; 
v_sz_boxed_1660_ = lean_unbox_usize(v_sz_1657_);
lean_dec(v_sz_1657_);
v_i_boxed_1661_ = lean_unbox_usize(v_i_1658_);
lean_dec(v_i_1658_);
v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_boxed_1660_, v_i_boxed_1661_, v_bs_1659_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_bs_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_bs_1665_);
return v___x_1672_;
}
else
{
uint8_t v___x_1673_; lean_object* v_v_1674_; lean_object* v___x_1675_; 
v___x_1673_ = 0;
v_v_1674_ = lean_array_uget_borrowed(v_bs_1665_, v_i_1664_);
lean_inc(v_v_1674_);
v___x_1675_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1674_, v___x_1673_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v_bs_x27_1678_; size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = lean_unsigned_to_nat(0u);
v_bs_x27_1678_ = lean_array_uset(v_bs_1665_, v_i_1664_, v___x_1677_);
v___x_1679_ = ((size_t)1ULL);
v___x_1680_ = lean_usize_add(v_i_1664_, v___x_1679_);
v___x_1681_ = lean_array_uset(v_bs_x27_1678_, v_i_1664_, v_a_1676_);
v_i_1664_ = v___x_1680_;
v_bs_1665_ = v___x_1681_;
goto _start;
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_bs_1665_);
v_a_1683_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1675_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1675_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1691_, lean_object* v_i_1692_, lean_object* v_bs_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1691_);
lean_dec(v_sz_1691_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1699_, v_i_boxed_1700_, v_bs_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_env_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v_env_1712_; lean_object* v_a_1714_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1711_ = lean_st_ref_get(v___y_1709_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_env_1712_);
lean_dec(v___x_1711_);
v___x_1724_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1702_, v___y_1707_, v___y_1709_);
lean_dec_ref(v___x_1724_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
v___x_1725_ = lean_apply_7(v_x_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, lean_box(0));
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1712_, v___y_1707_, v___y_1709_);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1727_, 0);
lean_dec(v_unused_1735_);
v___x_1729_ = v___x_1727_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v___x_1727_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_a_1726_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1726_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1736_; 
v_a_1736_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1725_, 1);
v_a_1714_ = v_a_1736_;
goto v___jp_1713_;
}
v___jp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v___x_1715_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1712_, v___y_1707_, v___y_1709_);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v___x_1715_, 0);
lean_dec(v_unused_1723_);
v___x_1717_ = v___x_1715_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_dec(v___x_1715_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 1);
lean_ctor_set(v___x_1717_, 0, v_a_1714_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1714_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_env_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_1737_, v_x_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1747_, lean_object* v_as_1748_, size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_a_1758_; uint8_t v___x_1762_; 
v___x_1762_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
lean_dec(v___x_1747_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_b_1751_);
return v___x_1763_;
}
else
{
lean_object* v_a_1764_; uint8_t v_kind_1765_; lean_object* v_declName_1766_; lean_object* v_type_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_a_1764_ = lean_array_uget_borrowed(v_as_1748_, v_i_1750_);
v_kind_1765_ = lean_ctor_get_uint8(v_a_1764_, sizeof(void*)*9);
v_declName_1766_ = lean_ctor_get(v_a_1764_, 3);
v_type_1767_ = lean_ctor_get(v_a_1764_, 6);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_name_eq(v_declName_1766_, v___x_1747_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
v___x_1770_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1765_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_inc_ref(v_type_1767_);
v___x_1771_ = l_Lean_Meta_isProp(v_type_1767_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; uint8_t v___x_1773_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = lean_unbox(v_a_1772_);
lean_dec(v_a_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_inc(v___x_1747_);
lean_inc(v_a_1764_);
v___x_1774_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1764_, v___x_1747_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_dec_ref_known(v___x_1774_, 1);
v_a_1758_ = v___x_1768_;
goto v___jp_1757_;
}
else
{
lean_dec(v___x_1747_);
return v___x_1774_;
}
}
else
{
v_a_1758_ = v___x_1768_;
goto v___jp_1757_;
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v___x_1747_);
v_a_1775_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1771_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1771_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
v_a_1758_ = v___x_1768_;
goto v___jp_1757_;
}
}
else
{
v_a_1758_ = v___x_1768_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
size_t v___x_1759_; size_t v___x_1760_; 
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1750_, v___x_1759_);
v_i_1750_ = v___x_1760_;
v_b_1751_ = v_a_1758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1783_, lean_object* v_as_1784_, lean_object* v_sz_1785_, lean_object* v_i_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
size_t v_sz_boxed_1793_; size_t v_i_boxed_1794_; lean_object* v_res_1795_; 
v_sz_boxed_1793_ = lean_unbox_usize(v_sz_1785_);
lean_dec(v_sz_1785_);
v_i_boxed_1794_ = lean_unbox_usize(v_i_1786_);
lean_dec(v_i_1786_);
v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1783_, v_as_1784_, v_sz_boxed_1793_, v_i_boxed_1794_, v_b_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_as_1784_);
return v_res_1795_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1816_, lean_object* v_preDefs_1817_, lean_object* v_termMeasure_x3fs_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v_sz_1826_ = lean_array_size(v_preDefs_1817_);
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_1826_, v___x_1827_, v_preDefs_1817_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; lean_object* v_env_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; size_t v_sz_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc_n(v_a_1829_, 2);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1830_ = lean_st_ref_get(v_a_1824_);
v_env_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc_ref(v_env_1831_);
lean_dec(v___x_1830_);
v___x_1832_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1833_ = lean_box(0);
v_sz_1847_ = lean_array_size(v_a_1829_);
v___x_1848_ = lean_box_usize(v_sz_1847_);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1850_, 0, v_a_1829_);
lean_closure_set(v___f_1850_, 1, v___x_1848_);
lean_closure_set(v___f_1850_, 2, v___x_1849_);
lean_closure_set(v___f_1850_, 3, v___x_1833_);
lean_closure_set(v___f_1850_, 4, v___x_1832_);
v___x_1851_ = l_Lean_Environment_unlockAsync(v_env_1831_);
v___x_1852_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1851_, v___f_1850_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v_snd_1854_; lean_object* v_fst_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_2042_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v_snd_1854_ = lean_ctor_get(v_a_1853_, 1);
v_fst_1855_ = lean_ctor_get(v_a_1853_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_1853_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_1857_ = v_a_1853_;
v_isShared_1858_ = v_isSharedCheck_2042_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_snd_1854_);
lean_inc(v_fst_1855_);
lean_dec(v_a_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_2042_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v_fst_1859_; lean_object* v_snd_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_2041_; 
v_fst_1859_ = lean_ctor_get(v_snd_1854_, 0);
v_snd_1860_ = lean_ctor_get(v_snd_1854_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_snd_1854_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_1862_ = v_snd_1854_;
v_isShared_1863_ = v_isSharedCheck_2041_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snd_1860_);
lean_inc(v_fst_1859_);
lean_dec(v_snd_1854_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_2041_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___x_1923_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v_wf_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v___f_1971_; size_t v_sz_1972_; lean_object* v_termMeasures_x3f_1973_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; uint8_t v___x_2034_; 
v___x_1923_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_1969_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1923_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
lean_inc(v_snd_1860_);
v___f_1971_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1971_, 0, v_snd_1860_);
v_sz_1972_ = lean_array_size(v_termMeasure_x3fs_1818_);
v_termMeasures_x3f_1973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_1972_, v___x_1827_, v_termMeasure_x3fs_1818_);
v___x_2034_ = lean_unbox(v_a_1970_);
lean_dec(v_a_1970_);
if (v___x_2034_ == 0)
{
v___y_1997_ = v_a_1819_;
v___y_1998_ = v_a_1820_;
v___y_1999_ = v_a_1821_;
v___y_2000_ = v_a_1822_;
v___y_2001_ = v_a_1823_;
v___y_2002_ = v_a_1824_;
goto v___jp_1996_;
}
else
{
lean_object* v_value_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_value_2035_ = lean_ctor_get(v_snd_1860_, 7);
v___x_2036_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2035_);
v___x_2037_ = l_Lean_MessageData_ofExpr(v_value_2035_);
v___x_2038_ = l_Lean_indentD(v___x_2037_);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1923_, v___x_2039_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec_ref_known(v___x_2040_, 1);
v___y_1997_ = v_a_1819_;
v___y_1998_ = v_a_1820_;
v___y_1999_ = v_a_1821_;
v___y_2000_ = v_a_1822_;
v___y_2001_ = v_a_1823_;
v___y_2002_ = v_a_1824_;
goto v___jp_1996_;
}
else
{
lean_dec(v_termMeasures_x3f_1973_);
lean_dec_ref(v___f_1971_);
lean_del_object(v___x_1862_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_del_object(v___x_1857_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
return v___x_2040_;
}
}
v___jp_1864_:
{
lean_object* v___x_1874_; 
lean_inc_ref(v___y_1867_);
lean_inc(v_a_1829_);
lean_inc(v_fst_1859_);
lean_inc(v_fst_1855_);
v___x_1874_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1855_, v_fst_1859_, v_a_1829_, v___y_1867_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
lean_inc_ref(v___y_1867_);
lean_inc(v_a_1829_);
lean_inc_ref(v_docCtx_1816_);
v___x_1876_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1816_, v_a_1829_, v_a_1875_, v___y_1867_, v___y_1865_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v_a_1875_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v___x_1877_; 
lean_dec_ref_known(v___x_1876_, 1);
lean_inc(v_a_1829_);
v___x_1877_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1816_, v_a_1829_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1878_; 
lean_dec_ref_known(v___x_1877_, 1);
v___x_1878_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1860_, v___y_1865_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1847_, v___x_1827_, v_a_1829_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_declName_1882_; lean_object* v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc_n(v_a_1881_, 2);
lean_dec_ref_known(v___x_1880_, 1);
v_declName_1882_ = lean_ctor_get(v___y_1867_, 3);
lean_inc_n(v_declName_1882_, 2);
lean_dec_ref(v___y_1867_);
v___x_1883_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1881_, v_declName_1882_, v_fst_1855_, v_fst_1859_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_declName_1884_; lean_object* v_type_1885_; lean_object* v___x_1886_; 
lean_dec_ref_known(v___x_1883_, 1);
v_declName_1884_ = lean_ctor_get(v_a_1879_, 3);
v_type_1885_ = lean_ctor_get(v_a_1879_, 6);
lean_inc(v_declName_1884_);
v___x_1886_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1884_, v___y_1873_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref_known(v___x_1886_, 1);
lean_inc_ref(v_type_1885_);
v___x_1887_ = l_Lean_Meta_isProp(v_type_1885_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; uint8_t v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = lean_unbox(v_a_1888_);
lean_dec(v_a_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_inc(v_declName_1882_);
v___x_1890_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1879_, v_declName_1882_, v___y_1866_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_dec_ref_known(v___x_1890_, 1);
v___y_1835_ = v_a_1881_;
v___y_1836_ = v_declName_1882_;
v___y_1837_ = v___y_1868_;
v___y_1838_ = v___y_1869_;
v___y_1839_ = v___y_1870_;
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1872_;
v___y_1842_ = v___y_1873_;
goto v___jp_1834_;
}
else
{
lean_dec(v_declName_1882_);
lean_dec(v_a_1881_);
return v___x_1890_;
}
}
else
{
lean_dec(v_a_1879_);
lean_dec_ref(v___y_1866_);
v___y_1835_ = v_a_1881_;
v___y_1836_ = v_declName_1882_;
v___y_1837_ = v___y_1868_;
v___y_1838_ = v___y_1869_;
v___y_1839_ = v___y_1870_;
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1872_;
v___y_1842_ = v___y_1873_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_declName_1882_);
lean_dec(v_a_1881_);
lean_dec(v_a_1879_);
lean_dec_ref(v___y_1866_);
v_a_1891_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1887_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1887_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_dec(v_declName_1882_);
lean_dec(v_a_1881_);
lean_dec(v_a_1879_);
lean_dec_ref(v___y_1866_);
return v___x_1886_;
}
}
else
{
lean_dec(v_declName_1882_);
lean_dec(v_a_1881_);
lean_dec(v_a_1879_);
lean_dec_ref(v___y_1866_);
return v___x_1883_;
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_a_1879_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_fst_1859_);
lean_dec(v_fst_1855_);
v_a_1899_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1880_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1880_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_fst_1859_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
v_a_1907_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1878_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1878_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
return v___x_1877_;
}
}
else
{
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
return v___x_1876_;
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
v_a_1915_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1874_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1874_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
v___jp_1924_:
{
lean_object* v_declName_1934_; lean_object* v_type_1935_; lean_object* v_numFixed_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
v_declName_1934_ = lean_ctor_get(v_snd_1860_, 3);
v_type_1935_ = lean_ctor_get(v_snd_1860_, 6);
v_numFixed_1936_ = lean_ctor_get(v_fst_1855_, 0);
v___x_1937_ = lean_box_usize(v_sz_1847_);
v___x_1938_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1855_);
lean_inc(v_declName_1934_);
lean_inc(v_fst_1859_);
lean_inc(v_snd_1860_);
lean_inc(v_a_1829_);
v___f_1939_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1939_, 0, v___x_1937_);
lean_closure_set(v___f_1939_, 1, v___x_1938_);
lean_closure_set(v___f_1939_, 2, v_a_1829_);
lean_closure_set(v___f_1939_, 3, v___y_1925_);
lean_closure_set(v___f_1939_, 4, v_snd_1860_);
lean_closure_set(v___f_1939_, 5, v_fst_1859_);
lean_closure_set(v___f_1939_, 6, v___x_1833_);
lean_closure_set(v___f_1939_, 7, v___x_1923_);
lean_closure_set(v___f_1939_, 8, v_declName_1934_);
lean_closure_set(v___f_1939_, 9, v_fst_1855_);
lean_closure_set(v___f_1939_, 10, v_wf_1927_);
lean_inc(v_numFixed_1936_);
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_numFixed_1936_);
v___x_1941_ = 0;
lean_inc_ref(v_type_1935_);
v___x_1942_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1935_, v___x_1940_, v___f_1939_, v___x_1941_, v___x_1941_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; uint8_t v___x_1946_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1923_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = lean_unbox(v_a_1945_);
lean_dec(v_a_1945_);
if (v___x_1946_ == 0)
{
lean_del_object(v___x_1862_);
lean_del_object(v___x_1857_);
v___y_1865_ = v___x_1941_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v_a_1943_;
v___y_1868_ = v___y_1928_;
v___y_1869_ = v___y_1929_;
v___y_1870_ = v___y_1930_;
v___y_1871_ = v___y_1931_;
v___y_1872_ = v___y_1932_;
v___y_1873_ = v___y_1933_;
goto v___jp_1864_;
}
else
{
lean_object* v_declName_1947_; lean_object* v_value_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_declName_1947_ = lean_ctor_get(v_a_1943_, 3);
v_value_1948_ = lean_ctor_get(v_a_1943_, 7);
v___x_1949_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1947_);
v___x_1950_ = l_Lean_MessageData_ofName(v_declName_1947_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 7);
lean_ctor_set(v___x_1862_, 1, v___x_1950_);
lean_ctor_set(v___x_1862_, 0, v___x_1949_);
v___x_1952_ = v___x_1862_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 7);
lean_ctor_set(v___x_1857_, 1, v___x_1953_);
lean_ctor_set(v___x_1857_, 0, v___x_1952_);
v___x_1955_ = v___x_1857_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_inc_ref(v_value_1948_);
v___x_1956_ = l_Lean_MessageData_ofExpr(v_value_1948_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1923_, v___x_1957_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref_known(v___x_1958_, 1);
v___y_1865_ = v___x_1941_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v_a_1943_;
v___y_1868_ = v___y_1928_;
v___y_1869_ = v___y_1929_;
v___y_1870_ = v___y_1930_;
v___y_1871_ = v___y_1931_;
v___y_1872_ = v___y_1932_;
v___y_1873_ = v___y_1933_;
goto v___jp_1864_;
}
else
{
lean_dec(v_a_1943_);
lean_dec_ref(v___y_1926_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
return v___x_1958_;
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v___y_1926_);
lean_del_object(v___x_1862_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_del_object(v___x_1857_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
v_a_1961_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1942_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1942_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
v___jp_1974_:
{
if (lean_obj_tag(v_termMeasures_x3f_1973_) == 1)
{
lean_object* v_val_1984_; 
lean_dec_ref(v___y_1976_);
v_val_1984_ = lean_ctor_get(v_termMeasures_x3f_1973_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v_termMeasures_x3f_1973_, 1);
v___y_1925_ = v___y_1975_;
v___y_1926_ = v___y_1977_;
v_wf_1927_ = v_val_1984_;
v___y_1928_ = v___y_1978_;
v___y_1929_ = v___y_1979_;
v___y_1930_ = v___y_1980_;
v___y_1931_ = v___y_1981_;
v___y_1932_ = v___y_1982_;
v___y_1933_ = v___y_1983_;
goto v___jp_1924_;
}
else
{
uint8_t v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v_termMeasures_x3f_1973_);
v___x_1985_ = 1;
v___x_1986_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1976_, v___x_1985_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___y_1925_ = v___y_1975_;
v___y_1926_ = v___y_1977_;
v_wf_1927_ = v_a_1987_;
v___y_1928_ = v___y_1978_;
v___y_1929_ = v___y_1979_;
v___y_1930_ = v___y_1980_;
v___y_1931_ = v___y_1981_;
v___y_1932_ = v___y_1982_;
v___y_1933_ = v___y_1983_;
goto v___jp_1924_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___y_1977_);
lean_dec_ref(v___y_1975_);
lean_del_object(v___x_1862_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_del_object(v___x_1857_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
v_a_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
v___jp_1996_:
{
lean_object* v___x_2003_; lean_object* v_env_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2003_ = lean_st_ref_get(v___y_2002_);
v_env_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc_ref(v_env_2004_);
lean_dec(v___x_2003_);
v___x_2005_ = l_Lean_Environment_unlockAsync(v_env_2004_);
v___x_2006_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_2005_, v___f_1971_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_fst_2008_; lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2025_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_fst_2008_ = lean_ctor_get(v_a_2007_, 0);
v_snd_2009_ = lean_ctor_get(v_a_2007_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2011_ = v_a_2007_;
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_inc(v_fst_2008_);
lean_dec(v_a_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v_a_2014_; lean_object* v___f_2015_; uint8_t v___x_2016_; 
v___x_2013_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1923_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
lean_inc(v_fst_1859_);
lean_inc(v_fst_1855_);
lean_inc(v_fst_2008_);
lean_inc(v_a_1829_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2015_, 0, v_a_1829_);
lean_closure_set(v___f_2015_, 1, v_fst_2008_);
lean_closure_set(v___f_2015_, 2, v_fst_1855_);
lean_closure_set(v___f_2015_, 3, v_fst_1859_);
v___x_2016_ = lean_unbox(v_a_2014_);
lean_dec(v_a_2014_);
if (v___x_2016_ == 0)
{
lean_del_object(v___x_2011_);
v___y_1975_ = v_fst_2008_;
v___y_1976_ = v___f_2015_;
v___y_1977_ = v_snd_2009_;
v___y_1978_ = v___y_1997_;
v___y_1979_ = v___y_1998_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_2001_;
v___y_1983_ = v___y_2002_;
goto v___jp_1974_;
}
else
{
lean_object* v_value_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v_value_2017_ = lean_ctor_get(v_snd_1860_, 7);
v___x_2018_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2017_);
v___x_2019_ = l_Lean_MessageData_ofExpr(v_value_2017_);
v___x_2020_ = l_Lean_indentD(v___x_2019_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 7);
lean_ctor_set(v___x_2011_, 1, v___x_2020_);
lean_ctor_set(v___x_2011_, 0, v___x_2018_);
v___x_2022_ = v___x_2011_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1923_, v___x_2022_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_dec_ref_known(v___x_2023_, 1);
v___y_1975_ = v_fst_2008_;
v___y_1976_ = v___f_2015_;
v___y_1977_ = v_snd_2009_;
v___y_1978_ = v___y_1997_;
v___y_1979_ = v___y_1998_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_2001_;
v___y_1983_ = v___y_2002_;
goto v___jp_1974_;
}
else
{
lean_dec_ref(v___f_2015_);
lean_dec(v_snd_2009_);
lean_dec(v_fst_2008_);
lean_dec(v_termMeasures_x3f_1973_);
lean_del_object(v___x_1862_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_del_object(v___x_1857_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_termMeasures_x3f_1973_);
lean_del_object(v___x_1862_);
lean_dec(v_snd_1860_);
lean_dec(v_fst_1859_);
lean_del_object(v___x_1857_);
lean_dec(v_fst_1855_);
lean_dec(v_a_1829_);
lean_dec_ref(v_docCtx_1816_);
v_a_2026_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2006_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2006_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_1829_);
lean_dec_ref(v_termMeasure_x3fs_1818_);
lean_dec_ref(v_docCtx_1816_);
v_a_2043_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_1852_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_1852_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
v___jp_1834_:
{
size_t v_sz_1843_; lean_object* v___x_1844_; 
v_sz_1843_ = lean_array_size(v___y_1835_);
lean_inc(v___y_1836_);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1836_, v___y_1835_, v_sz_1843_, v___x_1827_, v___x_1833_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1844_, 1);
v___x_1845_ = l_Lean_enableRealizationsForConst(v___y_1836_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1845_, 1);
v___x_1846_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1835_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1846_;
}
else
{
lean_dec_ref(v___y_1835_);
return v___x_1845_;
}
}
else
{
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_termMeasure_x3fs_1818_);
lean_dec_ref(v_docCtx_1816_);
v_a_2051_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1828_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1828_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2059_, lean_object* v_preDefs_2060_, lean_object* v_termMeasure_x3fs_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_wfRecursion(v_docCtx_2059_, v_preDefs_2060_, v_termMeasure_x3fs_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2070_, lean_object* v_msg_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_msg_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2080_, v_msg_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_2090_, size_t v_i_2091_, lean_object* v_bs_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_2090_, v_i_2091_, v_bs_2092_, v___y_2097_, v___y_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_2101_, lean_object* v_i_2102_, lean_object* v_bs_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
size_t v_sz_boxed_2111_; size_t v_i_boxed_2112_; lean_object* v_res_2113_; 
v_sz_boxed_2111_ = lean_unbox_usize(v_sz_2101_);
lean_dec(v_sz_2101_);
v_i_boxed_2112_ = lean_unbox_usize(v_i_2102_);
lean_dec(v_i_2102_);
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_2111_, v_i_boxed_2112_, v_bs_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object* v_as_2114_, size_t v_sz_2115_, size_t v_i_2116_, lean_object* v_b_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2114_, v_sz_2115_, v_i_2116_, v_b_2117_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_as_2126_, lean_object* v_sz_2127_, lean_object* v_i_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
size_t v_sz_boxed_2137_; size_t v_i_boxed_2138_; lean_object* v_res_2139_; 
v_sz_boxed_2137_ = lean_unbox_usize(v_sz_2127_);
lean_dec(v_sz_2127_);
v_i_boxed_2138_ = lean_unbox_usize(v_i_2128_);
lean_dec(v_i_2128_);
v_res_2139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_2126_, v_sz_boxed_2137_, v_i_boxed_2138_, v_b_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v_as_2126_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_a_2140_, lean_object* v_as_2141_, size_t v_sz_2142_, size_t v_i_2143_, lean_object* v_bs_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_2140_, v_sz_2142_, v_i_2143_, v_bs_2144_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_a_2153_, lean_object* v_as_2154_, lean_object* v_sz_2155_, lean_object* v_i_2156_, lean_object* v_bs_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
size_t v_sz_boxed_2165_; size_t v_i_boxed_2166_; lean_object* v_res_2167_; 
v_sz_boxed_2165_ = lean_unbox_usize(v_sz_2155_);
lean_dec(v_sz_2155_);
v_i_boxed_2166_ = lean_unbox_usize(v_i_2156_);
lean_dec(v_i_2156_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(v_a_2153_, v_as_2154_, v_sz_boxed_2165_, v_i_boxed_2166_, v_bs_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec_ref(v_as_2154_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object* v_a_2168_, lean_object* v___x_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_bs_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2168_, v___x_2169_, v_sz_2170_, v_i_2171_, v_bs_2172_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_a_2181_, lean_object* v___x_2182_, lean_object* v_sz_2183_, lean_object* v_i_2184_, lean_object* v_bs_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
size_t v_sz_boxed_2193_; size_t v_i_boxed_2194_; lean_object* v_res_2195_; 
v_sz_boxed_2193_ = lean_unbox_usize(v_sz_2183_);
lean_dec(v_sz_2183_);
v_i_boxed_2194_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_res_2195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_2181_, v___x_2182_, v_sz_boxed_2193_, v_i_boxed_2194_, v_bs_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_00_u03b1_2196_, lean_object* v_env_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_2197_, v_x_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_env_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(v_00_u03b1_2207_, v_env_2208_, v_x_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2218_, lean_object* v_msg_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2218_, v_msg_2219_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2228_, lean_object* v_msg_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2228_, v_msg_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2238_, size_t v_i_2239_, lean_object* v_bs_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2238_, v_i_2239_, v_bs_2240_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2249_, lean_object* v_i_2250_, lean_object* v_bs_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
size_t v_sz_boxed_2259_; size_t v_i_boxed_2260_; lean_object* v_res_2261_; 
v_sz_boxed_2259_ = lean_unbox_usize(v_sz_2249_);
lean_dec(v_sz_2249_);
v_i_boxed_2260_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2259_, v_i_boxed_2260_, v_bs_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2262_, lean_object* v_as_2263_, size_t v_sz_2264_, size_t v_i_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2262_, v_as_2263_, v_sz_2264_, v_i_2265_, v_b_2266_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2275_, lean_object* v_as_2276_, lean_object* v_sz_2277_, lean_object* v_i_2278_, lean_object* v_b_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
size_t v_sz_boxed_2287_; size_t v_i_boxed_2288_; lean_object* v_res_2289_; 
v_sz_boxed_2287_ = lean_unbox_usize(v_sz_2277_);
lean_dec(v_sz_2277_);
v_i_boxed_2288_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2275_, v_as_2276_, v_sz_boxed_2287_, v_i_boxed_2288_, v_b_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_as_2276_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2290_, lean_object* v_x_2291_, uint8_t v_isExporting_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2291_, v_isExporting_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2301_, lean_object* v_x_2302_, lean_object* v_isExporting_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
uint8_t v_isExporting_boxed_2311_; lean_object* v_res_2312_; 
v_isExporting_boxed_2311_ = lean_unbox(v_isExporting_2303_);
v_res_2312_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2301_, v_x_2302_, v_isExporting_boxed_2311_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2313_, lean_object* v_x_2314_, uint8_t v_when_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2314_, v_when_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2324_, lean_object* v_x_2325_, lean_object* v_when_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v_when_boxed_2334_; lean_object* v_res_2335_; 
v_when_boxed_2334_ = lean_unbox(v_when_2326_);
v_res_2335_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2324_, v_x_2325_, v_when_boxed_2334_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2336_, lean_object* v_macroStack_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2336_, v_macroStack_2337_, v___y_2342_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2346_, lean_object* v_macroStack_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2346_, v_macroStack_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2356_, lean_object* v_msgData_2357_, uint8_t v_severity_2358_, uint8_t v_isSilent_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2356_, v_msgData_2357_, v_severity_2358_, v_isSilent_2359_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2368_, lean_object* v_msgData_2369_, lean_object* v_severity_2370_, lean_object* v_isSilent_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v_severity_boxed_2379_; uint8_t v_isSilent_boxed_2380_; lean_object* v_res_2381_; 
v_severity_boxed_2379_ = lean_unbox(v_severity_2370_);
v_isSilent_boxed_2380_ = lean_unbox(v_isSilent_2371_);
v_res_2381_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2368_, v_msgData_2369_, v_severity_boxed_2379_, v_isSilent_boxed_2380_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v_ref_2368_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2453_ = 0;
v___x_2454_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2455_ = l_Lean_registerTraceClass(v___x_2452_, v___x_2453_, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2457_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
