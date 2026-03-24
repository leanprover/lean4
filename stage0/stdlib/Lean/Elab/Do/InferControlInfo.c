// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
static lean_once_cell_t l_Lean_Elab_Do_ControlInfo_pure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlInfo_pure___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_pure;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", exitsRegularly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ",\n    reassigns: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ",\n    returnsEarly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "breaks: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", continues: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value)} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 75, 74, 17, 172, 74, 138, 206)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 182, 102, 169, 76, 87, 55, 254)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 65, 144, 138, 55, 55, 217, 220)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ControlInfoHandler"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 126, 127, 228, 104, 205, 61, 148)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "control info inference"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 249, .m_capacity = 249, .m_length = 246, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `TSyntax \\`doElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Not a let or reassignment declaration: "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Not a catch or catch match: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; 
v___x_1_ = l_Lean_NameSet_empty;
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = 0;
v___x_4_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4_, 0, v___x_2_);
lean_ctor_set(v___x_4_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 1, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 2, v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = l_Lean_NameSet_empty;
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = 0;
v___x_10_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_7_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2, v___x_9_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2 + 1, v___x_9_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2 + 2, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
uint8_t v_breaks_14_; uint8_t v_continues_15_; uint8_t v_returnsEarly_16_; lean_object* v_numRegularExits_17_; lean_object* v_reassigns_18_; uint8_t v___y_20_; uint8_t v___y_21_; uint8_t v___y_22_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_breaks_14_ = lean_ctor_get_uint8(v_a_12_, sizeof(void*)*2);
v_continues_15_ = lean_ctor_get_uint8(v_a_12_, sizeof(void*)*2 + 1);
v_returnsEarly_16_ = lean_ctor_get_uint8(v_a_12_, sizeof(void*)*2 + 2);
v_numRegularExits_17_ = lean_ctor_get(v_a_12_, 0);
v_reassigns_18_ = lean_ctor_get(v_a_12_, 1);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_nat_dec_eq(v_numRegularExits_17_, v___x_33_);
if (v___x_34_ == 0)
{
uint8_t v___x_35_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_41_; 
lean_inc(v_reassigns_18_);
lean_dec_ref(v_a_12_);
v___x_35_ = 1;
if (v_breaks_14_ == 0)
{
uint8_t v_breaks_43_; 
v_breaks_43_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*2);
v___y_41_ = v_breaks_43_;
goto v___jp_40_;
}
else
{
v___y_41_ = v___x_35_;
goto v___jp_40_;
}
v___jp_36_:
{
if (v_returnsEarly_16_ == 0)
{
uint8_t v_returnsEarly_39_; 
v_returnsEarly_39_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*2 + 2);
v___y_20_ = v___y_37_;
v___y_21_ = v___y_38_;
v___y_22_ = v_returnsEarly_39_;
goto v___jp_19_;
}
else
{
v___y_20_ = v___y_37_;
v___y_21_ = v___y_38_;
v___y_22_ = v___x_35_;
goto v___jp_19_;
}
}
v___jp_40_:
{
if (v_continues_15_ == 0)
{
uint8_t v_continues_42_; 
v_continues_42_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*2 + 1);
v___y_37_ = v___y_41_;
v___y_38_ = v_continues_42_;
goto v___jp_36_;
}
else
{
v___y_37_ = v___y_41_;
v___y_38_ = v___x_35_;
goto v___jp_36_;
}
}
}
else
{
lean_dec_ref(v_b_13_);
return v_a_12_;
}
v___jp_19_:
{
lean_object* v_numRegularExits_23_; lean_object* v_reassigns_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_32_; 
v_numRegularExits_23_ = lean_ctor_get(v_b_13_, 0);
v_reassigns_24_ = lean_ctor_get(v_b_13_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_b_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_26_ = v_b_13_;
v_isShared_27_ = v_isSharedCheck_32_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_reassigns_24_);
lean_inc(v_numRegularExits_23_);
lean_dec(v_b_13_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_32_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_28_ = l_Lean_NameSet_append(v_reassigns_18_, v_reassigns_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_28_);
v___x_30_ = v___x_26_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_numRegularExits_23_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*2, v___y_20_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*2 + 1, v___y_21_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*2 + 2, v___y_22_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
uint8_t v_breaks_46_; uint8_t v_continues_47_; uint8_t v_returnsEarly_48_; lean_object* v_numRegularExits_49_; lean_object* v_reassigns_50_; uint8_t v___y_52_; uint8_t v___y_53_; uint8_t v___y_54_; uint8_t v___y_67_; uint8_t v___y_68_; uint8_t v___y_71_; 
v_breaks_46_ = lean_ctor_get_uint8(v_a_44_, sizeof(void*)*2);
v_continues_47_ = lean_ctor_get_uint8(v_a_44_, sizeof(void*)*2 + 1);
v_returnsEarly_48_ = lean_ctor_get_uint8(v_a_44_, sizeof(void*)*2 + 2);
v_numRegularExits_49_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_numRegularExits_49_);
v_reassigns_50_ = lean_ctor_get(v_a_44_, 1);
lean_inc(v_reassigns_50_);
lean_dec_ref(v_a_44_);
if (v_breaks_46_ == 0)
{
uint8_t v_breaks_73_; 
v_breaks_73_ = lean_ctor_get_uint8(v_b_45_, sizeof(void*)*2);
v___y_71_ = v_breaks_73_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_breaks_46_;
goto v___jp_70_;
}
v___jp_51_:
{
lean_object* v_numRegularExits_55_; lean_object* v_reassigns_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v_numRegularExits_55_ = lean_ctor_get(v_b_45_, 0);
v_reassigns_56_ = lean_ctor_get(v_b_45_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_b_45_);
if (v_isSharedCheck_65_ == 0)
{
v___x_58_ = v_b_45_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_reassigns_56_);
lean_inc(v_numRegularExits_55_);
lean_dec(v_b_45_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_60_ = lean_nat_add(v_numRegularExits_49_, v_numRegularExits_55_);
lean_dec(v_numRegularExits_55_);
lean_dec(v_numRegularExits_49_);
v___x_61_ = l_Lean_NameSet_append(v_reassigns_50_, v_reassigns_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_61_);
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2, v___y_52_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2 + 1, v___y_53_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2 + 2, v___y_54_);
return v___x_63_;
}
}
}
v___jp_66_:
{
if (v_returnsEarly_48_ == 0)
{
uint8_t v_returnsEarly_69_; 
v_returnsEarly_69_ = lean_ctor_get_uint8(v_b_45_, sizeof(void*)*2 + 2);
v___y_52_ = v___y_67_;
v___y_53_ = v___y_68_;
v___y_54_ = v_returnsEarly_69_;
goto v___jp_51_;
}
else
{
v___y_52_ = v___y_67_;
v___y_53_ = v___y_68_;
v___y_54_ = v_returnsEarly_48_;
goto v___jp_51_;
}
}
v___jp_70_:
{
if (v_continues_47_ == 0)
{
uint8_t v_continues_72_; 
v_continues_72_ = lean_ctor_get_uint8(v_b_45_, sizeof(void*)*2 + 1);
v___y_67_ = v___y_71_;
v___y_68_ = v_continues_72_;
goto v___jp_66_;
}
else
{
v___y_67_ = v___y_71_;
v___y_68_ = v_continues_47_;
goto v___jp_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_74_, lean_object* v_x2_75_, lean_object* v_x3_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_x1_74_);
lean_ctor_set(v___x_77_, 1, v_x3_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_80_ = l_Lean_stringToMessageData(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2));
v___x_83_ = l_Lean_stringToMessageData(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_106_ = l_Lean_stringToMessageData(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_111_ = l_Lean_stringToMessageData(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_115_, lean_object* v_info_116_){
_start:
{
uint8_t v_breaks_117_; uint8_t v_continues_118_; uint8_t v_returnsEarly_119_; lean_object* v_numRegularExits_120_; lean_object* v_reassigns_121_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v___x_153_; lean_object* v___y_155_; 
v_breaks_117_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*2);
v_continues_118_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*2 + 1);
v_returnsEarly_119_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*2 + 2);
v_numRegularExits_120_ = lean_ctor_get(v_info_116_, 0);
lean_inc(v_numRegularExits_120_);
v_reassigns_121_ = lean_ctor_get(v_info_116_, 1);
lean_inc(v_reassigns_121_);
lean_dec_ref(v_info_116_);
v___x_153_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
if (v_breaks_117_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_155_ = v___x_163_;
goto v___jp_154_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_155_ = v___x_164_;
goto v___jp_154_;
}
v___jp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_125_, 0, v___y_124_);
v___x_126_ = l_Lean_MessageData_ofFormat(v___x_125_);
v___x_127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_123_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Nat_reprFast(v_numRegularExits_120_);
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___x_132_ = l_Lean_MessageData_ofFormat(v___x_131_);
v___x_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_129_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_box(0);
v___x_137_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_138_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_137_, v___f_115_, v___x_136_, v_reassigns_121_);
v___x_139_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14));
v___x_140_ = l_List_mapTR_loop___redArg(v___x_139_, v___x_138_, v___x_136_);
v___x_141_ = l_Lean_MessageData_ofList(v___x_140_);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_135_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
return v___x_142_;
}
v___jp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___y_145_);
v___x_147_ = l_Lean_MessageData_ofFormat(v___x_146_);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___y_144_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
if (v_returnsEarly_119_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_123_ = v___x_150_;
v___y_124_ = v___x_151_;
goto v___jp_122_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_123_ = v___x_150_;
v___y_124_ = v___x_152_;
goto v___jp_122_;
}
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_156_, 0, v___y_155_);
v___x_157_ = l_Lean_MessageData_ofFormat(v___x_156_);
v___x_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_153_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
v___x_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
if (v_continues_118_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_144_ = v___x_160_;
v___y_145_ = v___x_161_;
goto v___jp_143_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_144_ = v___x_160_;
v___y_145_ = v___x_162_;
goto v___jp_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_193_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_196_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_197_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_198_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_199_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_200_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_195_, v___x_196_, v___x_197_, v___x_198_, v___x_199_, v_ref_193_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_212_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_218_ = ((lean_object*)(l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_219_ = l_Lean_addBuiltinDocString(v___x_217_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_249_ = ((lean_object*)(l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_250_ = l_Lean_addBuiltinDeclarationRanges(v___x_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_252_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_box(1);
v___x_254_ = l_Lean_MessageData_ofFormat(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2));
v___x_259_ = l_Lean_MessageData_ofFormat(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
return v_x_260_;
}
else
{
lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_285_; 
v_head_262_ = lean_ctor_get(v_x_261_, 0);
v_tail_263_ = lean_ctor_get(v_x_261_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_285_ == 0)
{
v___x_265_ = v_x_261_;
v_isShared_266_ = v_isSharedCheck_285_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_tail_263_);
lean_inc(v_head_262_);
lean_dec(v_x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_285_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_before_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_283_; 
v_before_267_ = lean_ctor_get(v_head_262_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_head_262_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_head_262_, 1);
lean_dec(v_unused_284_);
v___x_269_ = v_head_262_;
v_isShared_270_ = v_isSharedCheck_283_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_before_267_);
lean_dec(v_head_262_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_283_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
if (v_isShared_270_ == 0)
{
lean_ctor_set_tag(v___x_269_, 7);
lean_ctor_set(v___x_269_, 1, v___x_271_);
lean_ctor_set(v___x_269_, 0, v_x_260_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_x_260_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_282_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 7);
lean_ctor_set(v___x_265_, 1, v___x_274_);
lean_ctor_set(v___x_265_, 0, v___x_273_);
v___x_276_ = v___x_265_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_281_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = l_Lean_MessageData_ofSyntax(v_before_267_);
v___x_278_ = l_Lean_indentD(v___x_277_);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v_x_260_ = v___x_279_;
v_x_261_ = v_tail_263_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(lean_object* v_opts_286_, lean_object* v_opt_287_){
_start:
{
lean_object* v_name_288_; lean_object* v_defValue_289_; lean_object* v_map_290_; lean_object* v___x_291_; 
v_name_288_ = lean_ctor_get(v_opt_287_, 0);
v_defValue_289_ = lean_ctor_get(v_opt_287_, 1);
v_map_290_ = lean_ctor_get(v_opts_286_, 0);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_290_, v_name_288_);
if (lean_obj_tag(v___x_291_) == 0)
{
uint8_t v___x_292_; 
v___x_292_ = lean_unbox(v_defValue_289_);
return v___x_292_;
}
else
{
lean_object* v_val_293_; 
v_val_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_293_);
lean_dec_ref(v___x_291_);
if (lean_obj_tag(v_val_293_) == 1)
{
uint8_t v_v_294_; 
v_v_294_ = lean_ctor_get_uint8(v_val_293_, 0);
lean_dec_ref(v_val_293_);
return v_v_294_;
}
else
{
uint8_t v___x_295_; 
lean_dec(v_val_293_);
v___x_295_ = lean_unbox(v_defValue_289_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20___boxed(lean_object* v_opts_296_, lean_object* v_opt_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(v_opts_296_, v_opt_297_);
lean_dec_ref(v_opt_297_);
lean_dec_ref(v_opts_296_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1));
v___x_304_ = l_Lean_MessageData_ofFormat(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(lean_object* v_msgData_305_, lean_object* v_macroStack_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_options_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_options_309_ = lean_ctor_get(v___y_307_, 2);
v___x_310_ = l_Lean_Elab_pp_macroStack;
v___x_311_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(v_options_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec(v_macroStack_306_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_msgData_305_);
return v___x_312_;
}
else
{
if (lean_obj_tag(v_macroStack_306_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v_msgData_305_);
return v___x_313_;
}
else
{
lean_object* v_head_314_; lean_object* v_after_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_330_; 
v_head_314_ = lean_ctor_get(v_macroStack_306_, 0);
lean_inc(v_head_314_);
v_after_315_ = lean_ctor_get(v_head_314_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_head_314_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_head_314_, 0);
lean_dec(v_unused_331_);
v___x_317_ = v_head_314_;
v_isShared_318_ = v_isSharedCheck_330_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_after_315_);
lean_dec(v_head_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_330_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 7);
lean_ctor_set(v___x_317_, 1, v___x_319_);
lean_ctor_set(v___x_317_, 0, v_msgData_305_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_msgData_305_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_319_);
v___x_321_ = v_reuseFailAlloc_329_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_msgData_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_322_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2);
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_MessageData_ofSyntax(v_after_315_);
v___x_325_ = l_Lean_indentD(v___x_324_);
v_msgData_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_326_, 0, v___x_323_);
lean_ctor_set(v_msgData_326_, 1, v___x_325_);
v___x_327_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(v_msgData_326_, v_macroStack_306_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___boxed(lean_object* v_msgData_332_, lean_object* v_macroStack_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(v_msgData_332_, v_macroStack_333_, v___y_334_);
lean_dec_ref(v___y_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_mctx_346_; lean_object* v_lctx_347_; lean_object* v_options_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_343_ = lean_st_ref_get(v___y_341_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = lean_st_ref_get(v___y_339_);
v_mctx_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_mctx_346_);
lean_dec(v___x_345_);
v_lctx_347_ = lean_ctor_get(v___y_338_, 2);
v_options_348_ = lean_ctor_get(v___y_340_, 2);
lean_inc_ref(v_options_348_);
lean_inc_ref(v_lctx_347_);
v___x_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_349_, 0, v_env_344_);
lean_ctor_set(v___x_349_, 1, v_mctx_346_);
lean_ctor_set(v___x_349_, 2, v_lctx_347_);
lean_ctor_set(v___x_349_, 3, v_options_348_);
v___x_350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_msgData_337_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_ref_367_; lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v_macroStack_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_ref_367_ = lean_ctor_get(v___y_364_, 5);
v___x_368_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msg_359_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v_macroStack_370_ = lean_ctor_get(v___y_360_, 1);
lean_inc(v_macroStack_370_);
lean_dec_ref(v___y_360_);
lean_inc(v_macroStack_370_);
v___x_371_ = l_Lean_Elab_getBetterRef(v_ref_367_, v_macroStack_370_);
v___x_372_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(v_a_369_, v_macroStack_370_, v___y_364_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_371_);
lean_ctor_set(v___x_377_, 1, v_a_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_, lean_object* v_b_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; 
v___x_396_ = lean_array_uget_borrowed(v_as_391_, v_i_392_);
lean_inc(v___x_396_);
v___x_397_ = l_Lean_NameSet_insert(v_b_394_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_392_, v___x_398_);
v_i_392_ = v___x_399_;
v_b_394_ = v___x_397_;
goto _start;
}
else
{
return v_b_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_stop_403_, lean_object* v_b_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; lean_object* v_res_407_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_403_);
lean_dec(v_stop_403_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_401_, v_i_boxed_405_, v_stop_boxed_406_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_408_, size_t v_i_409_, lean_object* v_bs_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_lt(v_i_409_, v_sz_408_);
if (v___x_411_ == 0)
{
return v_bs_410_;
}
else
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_bs_x27_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v_v_412_ = lean_array_uget(v_bs_410_, v_i_409_);
v___x_413_ = lean_unsigned_to_nat(0u);
v_bs_x27_414_ = lean_array_uset(v_bs_410_, v_i_409_, v___x_413_);
v___x_415_ = l_Lean_TSyntax_getId(v_v_412_);
lean_dec(v_v_412_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_i_409_, v___x_416_);
v___x_418_ = lean_array_uset(v_bs_x27_414_, v_i_409_, v___x_415_);
v_i_409_ = v___x_417_;
v_bs_410_ = v___x_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_420_, lean_object* v_i_421_, lean_object* v_bs_422_){
_start:
{
size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v_sz_boxed_423_ = lean_unbox_usize(v_sz_420_);
lean_dec(v_sz_420_);
v_i_boxed_424_ = lean_unbox_usize(v_i_421_);
lean_dec(v_i_421_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_423_, v_i_boxed_424_, v_bs_422_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
v___x_427_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_434_, size_t v_i_435_, lean_object* v_bs_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v_bs_436_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v_bs_x27_440_; lean_object* v___x_441_; size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v_bs_x27_440_ = lean_array_uset(v_bs_436_, v_i_435_, v___x_439_);
v___x_441_ = lean_box(0);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_435_, v___x_442_);
v___x_444_ = lean_array_uset(v_bs_x27_440_, v_i_435_, v___x_441_);
v_i_435_ = v___x_443_;
v_bs_436_ = v___x_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_446_, lean_object* v_i_447_, lean_object* v_bs_448_){
_start:
{
size_t v_sz_boxed_449_; size_t v_i_boxed_450_; lean_object* v_res_451_; 
v_sz_boxed_449_ = lean_unbox_usize(v_sz_446_);
lean_dec(v_sz_446_);
v_i_boxed_450_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_449_, v_i_boxed_450_, v_bs_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_452_, uint8_t v___x_453_, lean_object* v_as_454_, size_t v_i_455_, size_t v_stop_456_, lean_object* v_b_457_){
_start:
{
lean_object* v___y_459_; uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_eq(v_i_455_, v_stop_456_);
if (v___x_463_ == 0)
{
lean_object* v_fst_464_; uint8_t v___x_465_; 
v_fst_464_ = lean_ctor_get(v_b_457_, 0);
v___x_465_ = lean_unbox(v_fst_464_);
if (v___x_465_ == 0)
{
lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_snd_466_ = lean_ctor_get(v_b_457_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_b_457_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_b_457_, 0);
lean_dec(v_unused_475_);
v___x_468_ = v_b_457_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_dec(v_b_457_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_box(v___x_452_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_466_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v___y_459_ = v___x_472_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v_snd_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_486_; 
v_snd_476_ = lean_ctor_get(v_b_457_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_b_457_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_b_457_, 0);
lean_dec(v_unused_487_);
v___x_478_ = v_b_457_;
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snd_476_);
lean_dec(v_b_457_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_480_ = lean_array_uget_borrowed(v_as_454_, v_i_455_);
lean_inc(v___x_480_);
v___x_481_ = lean_array_push(v_snd_476_, v___x_480_);
v___x_482_ = lean_box(v___x_453_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_481_);
lean_ctor_set(v___x_478_, 0, v___x_482_);
v___x_484_ = v___x_478_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_481_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v___y_459_ = v___x_484_;
goto v___jp_458_;
}
}
}
}
else
{
return v_b_457_;
}
v___jp_458_:
{
size_t v___x_460_; size_t v___x_461_; 
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_455_, v___x_460_);
v_i_455_ = v___x_461_;
v_b_457_ = v___y_459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v_as_490_, lean_object* v_i_491_, lean_object* v_stop_492_, lean_object* v_b_493_){
_start:
{
uint8_t v___x_258750__boxed_494_; uint8_t v___x_258751__boxed_495_; size_t v_i_boxed_496_; size_t v_stop_boxed_497_; lean_object* v_res_498_; 
v___x_258750__boxed_494_ = lean_unbox(v___x_488_);
v___x_258751__boxed_495_ = lean_unbox(v___x_489_);
v_i_boxed_496_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_497_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_258750__boxed_494_, v___x_258751__boxed_495_, v_as_490_, v_i_boxed_496_, v_stop_boxed_497_, v_b_493_);
lean_dec_ref(v_as_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_499_, lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_fileName_508_; lean_object* v_fileMap_509_; lean_object* v_options_510_; lean_object* v_currRecDepth_511_; lean_object* v_maxRecDepth_512_; lean_object* v_ref_513_; lean_object* v_currNamespace_514_; lean_object* v_openDecls_515_; lean_object* v_initHeartbeats_516_; lean_object* v_maxHeartbeats_517_; lean_object* v_quotContext_518_; lean_object* v_currMacroScope_519_; uint8_t v_diag_520_; lean_object* v_cancelTk_x3f_521_; uint8_t v_suppressElabErrors_522_; lean_object* v_inheritedTraceOptions_523_; lean_object* v_ref_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_fileName_508_ = lean_ctor_get(v___y_505_, 0);
v_fileMap_509_ = lean_ctor_get(v___y_505_, 1);
v_options_510_ = lean_ctor_get(v___y_505_, 2);
v_currRecDepth_511_ = lean_ctor_get(v___y_505_, 3);
v_maxRecDepth_512_ = lean_ctor_get(v___y_505_, 4);
v_ref_513_ = lean_ctor_get(v___y_505_, 5);
v_currNamespace_514_ = lean_ctor_get(v___y_505_, 6);
v_openDecls_515_ = lean_ctor_get(v___y_505_, 7);
v_initHeartbeats_516_ = lean_ctor_get(v___y_505_, 8);
v_maxHeartbeats_517_ = lean_ctor_get(v___y_505_, 9);
v_quotContext_518_ = lean_ctor_get(v___y_505_, 10);
v_currMacroScope_519_ = lean_ctor_get(v___y_505_, 11);
v_diag_520_ = lean_ctor_get_uint8(v___y_505_, sizeof(void*)*14);
v_cancelTk_x3f_521_ = lean_ctor_get(v___y_505_, 12);
v_suppressElabErrors_522_ = lean_ctor_get_uint8(v___y_505_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_523_ = lean_ctor_get(v___y_505_, 13);
v_ref_524_ = l_Lean_replaceRef(v_ref_499_, v_ref_513_);
lean_inc_ref(v_inheritedTraceOptions_523_);
lean_inc(v_cancelTk_x3f_521_);
lean_inc(v_currMacroScope_519_);
lean_inc(v_quotContext_518_);
lean_inc(v_maxHeartbeats_517_);
lean_inc(v_initHeartbeats_516_);
lean_inc(v_openDecls_515_);
lean_inc(v_currNamespace_514_);
lean_inc(v_maxRecDepth_512_);
lean_inc(v_currRecDepth_511_);
lean_inc_ref(v_options_510_);
lean_inc_ref(v_fileMap_509_);
lean_inc_ref(v_fileName_508_);
v___x_525_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_525_, 0, v_fileName_508_);
lean_ctor_set(v___x_525_, 1, v_fileMap_509_);
lean_ctor_set(v___x_525_, 2, v_options_510_);
lean_ctor_set(v___x_525_, 3, v_currRecDepth_511_);
lean_ctor_set(v___x_525_, 4, v_maxRecDepth_512_);
lean_ctor_set(v___x_525_, 5, v_ref_524_);
lean_ctor_set(v___x_525_, 6, v_currNamespace_514_);
lean_ctor_set(v___x_525_, 7, v_openDecls_515_);
lean_ctor_set(v___x_525_, 8, v_initHeartbeats_516_);
lean_ctor_set(v___x_525_, 9, v_maxHeartbeats_517_);
lean_ctor_set(v___x_525_, 10, v_quotContext_518_);
lean_ctor_set(v___x_525_, 11, v_currMacroScope_519_);
lean_ctor_set(v___x_525_, 12, v_cancelTk_x3f_521_);
lean_ctor_set(v___x_525_, 13, v_inheritedTraceOptions_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*14, v_diag_520_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*14 + 1, v_suppressElabErrors_522_);
lean_inc_ref(v___y_501_);
v___x_526_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___x_525_, v___y_506_);
lean_dec_ref(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_527_, lean_object* v_msg_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_527_, v_msg_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v_ref_527_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_537_, lean_object* v_declName_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___x_541_; lean_object* v_env_542_; lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_541_ = 0;
v_env_542_ = l_Lean_Environment_setExporting(v_env_537_, v___x_541_);
lean_inc(v_declName_538_);
v___x_543_ = l_Lean_mkPrivateName(v_env_542_, v_declName_538_);
v___x_544_ = 1;
lean_inc_ref(v_env_542_);
v___x_545_ = l_Lean_Environment_contains(v_env_542_, v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = l_Lean_privateToUserName(v_declName_538_);
v___x_547_ = l_Lean_Environment_contains(v_env_542_, v___x_546_, v___x_544_);
v___x_548_ = lean_box(v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___y_540_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v_env_542_);
lean_dec(v_declName_538_);
v___x_550_ = lean_box(v___x_545_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___y_540_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_552_, lean_object* v_declName_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_552_, v_declName_553_, v___y_554_, v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = l_Lean_maxRecDepthErrorMessage;
v___x_563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3);
v___x_565_ = l_Lean_MessageData_ofFormat(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4);
v___x_567_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2));
v___x_568_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(lean_object* v_ref_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_ref_569_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___boxed(lean_object* v_ref_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(v_ref_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_577_, lean_object* v___y_578_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_579_);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v_a_579_);
lean_ctor_set(v___x_580_, 1, v___y_578_);
return v___x_580_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_581_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_a_581_);
lean_ctor_set(v___x_582_, 1, v___y_578_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_583_, v___y_584_);
lean_dec_ref(v_x_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_586_, lean_object* v_stx_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_586_, v_stx_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
if (lean_obj_tag(v_a_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_a_592_ = lean_ctor_get(v___x_590_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_601_);
v___x_594_ = v___x_590_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_590_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_box(0);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_a_592_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_val_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_630_; 
v_val_602_ = lean_ctor_get(v_a_591_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_591_);
if (v_isSharedCheck_630_ == 0)
{
v___x_604_ = v_a_591_;
v_isShared_605_ = v_isSharedCheck_630_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_val_602_);
lean_dec(v_a_591_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_630_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_snd_606_; 
v_snd_606_ = lean_ctor_get(v_val_602_, 1);
lean_inc(v_snd_606_);
lean_dec(v_val_602_);
if (lean_obj_tag(v_snd_606_) == 0)
{
lean_object* v_a_607_; lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
lean_del_object(v___x_604_);
v_a_607_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_a_607_);
lean_dec_ref(v___x_590_);
v_a_608_ = lean_ctor_get(v_snd_606_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_snd_606_);
if (v_isSharedCheck_616_ == 0)
{
v___x_610_ = v_snd_606_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v_snd_606_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_613_, v_a_607_);
lean_dec_ref(v___x_613_);
return v___x_614_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_629_; 
v_a_617_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_a_617_);
lean_dec_ref(v___x_590_);
v_a_618_ = lean_ctor_get(v_snd_606_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_snd_606_);
if (v_isSharedCheck_629_ == 0)
{
v___x_620_ = v_snd_606_;
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v_snd_606_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_a_618_);
v___x_623_ = v___x_604_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_628_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_623_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_627_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; 
v___x_626_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_625_, v_a_617_);
lean_dec_ref(v___x_625_);
return v___x_626_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_631_ = lean_ctor_get(v___x_590_, 0);
v_a_632_ = lean_ctor_get(v___x_590_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_590_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_inc(v_a_631_);
lean_dec(v___x_590_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_631_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_640_, lean_object* v_stx_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_640_, v_stx_641_, v___y_642_, v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_644_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(lean_object* v_keys_645_, lean_object* v_i_646_, lean_object* v_k_647_){
_start:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_array_get_size(v_keys_645_);
v___x_649_ = lean_nat_dec_lt(v_i_646_, v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v_i_646_);
return v___x_649_;
}
else
{
lean_object* v_k_x27_650_; uint8_t v___x_651_; 
v_k_x27_650_ = lean_array_fget_borrowed(v_keys_645_, v_i_646_);
v___x_651_ = l_Lean_instBEqExtraModUse_beq(v_k_647_, v_k_x27_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_i_646_, v___x_652_);
lean_dec(v_i_646_);
v_i_646_ = v___x_653_;
goto _start;
}
else
{
lean_dec(v_i_646_);
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg___boxed(lean_object* v_keys_655_, lean_object* v_i_656_, lean_object* v_k_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(v_keys_655_, v_i_656_, v_k_657_);
lean_dec_ref(v_k_657_);
lean_dec_ref(v_keys_655_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0(void){
_start:
{
size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; 
v___x_660_ = ((size_t)5ULL);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_shift_left(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1(void){
_start:
{
size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; 
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0);
v___x_665_ = lean_usize_sub(v___x_664_, v___x_663_);
return v___x_665_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(lean_object* v_x_666_, size_t v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
lean_object* v_es_669_; lean_object* v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; lean_object* v_j_674_; lean_object* v___x_675_; 
v_es_669_ = lean_ctor_get(v_x_666_, 0);
lean_inc_ref(v_es_669_);
lean_dec_ref(v_x_666_);
v___x_670_ = lean_box(2);
v___x_671_ = ((size_t)5ULL);
v___x_672_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1);
v___x_673_ = lean_usize_land(v_x_667_, v___x_672_);
v_j_674_ = lean_usize_to_nat(v___x_673_);
v___x_675_ = lean_array_get(v___x_670_, v_es_669_, v_j_674_);
lean_dec(v_j_674_);
lean_dec_ref(v_es_669_);
switch(lean_obj_tag(v___x_675_))
{
case 0:
{
lean_object* v_key_676_; uint8_t v___x_677_; 
v_key_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_key_676_);
lean_dec_ref(v___x_675_);
v___x_677_ = l_Lean_instBEqExtraModUse_beq(v_x_668_, v_key_676_);
lean_dec(v_key_676_);
return v___x_677_;
}
case 1:
{
lean_object* v_node_678_; size_t v___x_679_; 
v_node_678_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_node_678_);
lean_dec_ref(v___x_675_);
v___x_679_ = lean_usize_shift_right(v_x_667_, v___x_671_);
v_x_666_ = v_node_678_;
v_x_667_ = v___x_679_;
goto _start;
}
default: 
{
uint8_t v___x_681_; 
v___x_681_ = 0;
return v___x_681_;
}
}
}
else
{
lean_object* v_ks_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_ks_682_ = lean_ctor_get(v_x_666_, 0);
lean_inc_ref(v_ks_682_);
lean_dec_ref(v_x_666_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(v_ks_682_, v___x_683_, v_x_668_);
lean_dec_ref(v_ks_682_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___boxed(lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
size_t v_x_259057__boxed_688_; uint8_t v_res_689_; lean_object* v_r_690_; 
v_x_259057__boxed_688_ = lean_unbox_usize(v_x_686_);
lean_dec(v_x_686_);
v_res_689_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(v_x_685_, v_x_259057__boxed_688_, v_x_687_);
lean_dec_ref(v_x_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
uint64_t v___x_693_; size_t v___x_694_; uint8_t v___x_695_; 
v___x_693_ = l_Lean_instHashableExtraModUse_hash(v_x_692_);
v___x_694_ = lean_uint64_to_usize(v___x_693_);
v___x_695_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(v_x_691_, v___x_694_, v_x_692_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg___boxed(lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(v_x_696_, v_x_697_);
lean_dec_ref(v_x_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_700_; double v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_float_of_nat(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(lean_object* v_cls_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_ref_712_; lean_object* v___x_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_758_; 
v_ref_712_ = lean_ctor_get(v___y_709_, 5);
v___x_713_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msg_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_758_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_758_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_758_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v_traceState_719_; lean_object* v_env_720_; lean_object* v_nextMacroScope_721_; lean_object* v_ngen_722_; lean_object* v_auxDeclNGen_723_; lean_object* v_cache_724_; lean_object* v_messages_725_; lean_object* v_infoState_726_; lean_object* v_snapshotTasks_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_757_; 
v___x_718_ = lean_st_ref_take(v___y_710_);
v_traceState_719_ = lean_ctor_get(v___x_718_, 4);
v_env_720_ = lean_ctor_get(v___x_718_, 0);
v_nextMacroScope_721_ = lean_ctor_get(v___x_718_, 1);
v_ngen_722_ = lean_ctor_get(v___x_718_, 2);
v_auxDeclNGen_723_ = lean_ctor_get(v___x_718_, 3);
v_cache_724_ = lean_ctor_get(v___x_718_, 5);
v_messages_725_ = lean_ctor_get(v___x_718_, 6);
v_infoState_726_ = lean_ctor_get(v___x_718_, 7);
v_snapshotTasks_727_ = lean_ctor_get(v___x_718_, 8);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_757_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_757_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snapshotTasks_727_);
lean_inc(v_infoState_726_);
lean_inc(v_messages_725_);
lean_inc(v_cache_724_);
lean_inc(v_traceState_719_);
lean_inc(v_auxDeclNGen_723_);
lean_inc(v_ngen_722_);
lean_inc(v_nextMacroScope_721_);
lean_inc(v_env_720_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_757_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint64_t v_tid_731_; lean_object* v_traces_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_756_; 
v_tid_731_ = lean_ctor_get_uint64(v_traceState_719_, sizeof(void*)*1);
v_traces_732_ = lean_ctor_get(v_traceState_719_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_traceState_719_);
if (v_isSharedCheck_756_ == 0)
{
v___x_734_ = v_traceState_719_;
v_isShared_735_ = v_isSharedCheck_756_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_traces_732_);
lean_dec(v_traceState_719_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_756_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; double v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_736_ = lean_box(0);
v___x_737_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0);
v___x_738_ = 0;
v___x_739_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
v___x_740_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_740_, 0, v_cls_705_);
lean_ctor_set(v___x_740_, 1, v___x_736_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
lean_ctor_set_float(v___x_740_, sizeof(void*)*3, v___x_737_);
lean_ctor_set_float(v___x_740_, sizeof(void*)*3 + 8, v___x_737_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*3 + 16, v___x_738_);
v___x_741_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2));
v___x_742_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v_a_714_);
lean_ctor_set(v___x_742_, 2, v___x_741_);
lean_inc(v_ref_712_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_ref_712_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_PersistentArray_push___redArg(v_traces_732_, v___x_743_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_744_);
v___x_746_ = v___x_734_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_744_);
lean_ctor_set_uint64(v_reuseFailAlloc_755_, sizeof(void*)*1, v_tid_731_);
v___x_746_ = v_reuseFailAlloc_755_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 4, v___x_746_);
v___x_748_ = v___x_729_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_env_720_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_nextMacroScope_721_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_ngen_722_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_auxDeclNGen_723_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_754_, 5, v_cache_724_);
lean_ctor_set(v_reuseFailAlloc_754_, 6, v_messages_725_);
lean_ctor_set(v_reuseFailAlloc_754_, 7, v_infoState_726_);
lean_ctor_set(v_reuseFailAlloc_754_, 8, v_snapshotTasks_727_);
v___x_748_ = v_reuseFailAlloc_754_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_749_ = lean_st_ref_set(v___y_710_, v___x_748_);
v___x_750_ = lean_box(0);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_750_);
v___x_752_ = v___x_716_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___boxed(lean_object* v_cls_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(v_cls_759_, v_msg_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_options_773_; uint8_t v_hasTrace_774_; 
v_options_773_ = lean_ctor_get(v___y_771_, 2);
v_hasTrace_774_ = lean_ctor_get_uint8(v_options_773_, sizeof(void*)*1);
if (v_hasTrace_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v_cls_770_);
v___x_775_ = lean_box(v_hasTrace_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
else
{
lean_object* v_inheritedTraceOptions_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_inheritedTraceOptions_777_ = lean_ctor_get(v___y_771_, 13);
v___x_778_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_779_ = l_Lean_Name_append(v___x_778_, v_cls_770_);
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_777_, v_options_773_, v___x_779_);
lean_dec(v___x_779_);
v___x_781_ = lean_box(v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_783_, v___y_784_);
lean_dec_ref(v___y_784_);
return v_res_786_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1));
v___x_790_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0));
v___x_791_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_790_, v___x_789_);
return v___x_791_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4);
v___x_798_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
lean_ctor_set(v___x_798_, 2, v___x_797_);
lean_ctor_set(v___x_798_, 3, v___x_797_);
lean_ctor_set(v___x_798_, 4, v___x_797_);
lean_ctor_set(v___x_798_, 5, v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(lean_object* v_mod_820_, uint8_t v_isMeta_821_, lean_object* v_hint_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_env_831_; uint8_t v_isExporting_832_; lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v___x_835_; lean_object* v_entry_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_830_ = lean_st_ref_get(v___y_828_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_env_831_);
lean_dec(v___x_830_);
v_isExporting_832_ = lean_ctor_get_uint8(v_env_831_, sizeof(void*)*8);
lean_dec_ref(v_env_831_);
v___x_833_ = lean_st_ref_get(v___y_828_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_env_834_);
lean_dec(v___x_833_);
v___x_835_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2);
lean_inc(v_mod_820_);
v_entry_836_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_836_, 0, v_mod_820_);
lean_ctor_set_uint8(v_entry_836_, sizeof(void*)*1, v_isExporting_832_);
lean_ctor_set_uint8(v_entry_836_, sizeof(void*)*1 + 1, v_isMeta_821_);
v___x_837_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_838_ = lean_box(1);
v___x_839_ = lean_box(0);
v___x_882_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_835_, v___x_837_, v_env_834_, v___x_838_, v___x_839_);
v___x_883_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(v___x_882_, v_entry_836_);
if (v___x_883_ == 0)
{
lean_object* v_cls_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___x_906_; 
v_cls_884_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8));
v___x_885_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_884_, v___y_827_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v___x_906_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
if (v___x_906_ == 0)
{
lean_dec(v_hint_822_);
lean_dec(v_mod_820_);
v___y_841_ = v___y_826_;
v___y_842_ = v___y_828_;
goto v___jp_840_;
}
else
{
lean_object* v___x_907_; lean_object* v___y_909_; 
v___x_907_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15);
if (v_isExporting_832_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20));
v___y_909_ = v___x_916_;
goto v___jp_908_;
}
else
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21));
v___y_909_ = v___x_917_;
goto v___jp_908_;
}
v___jp_908_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = l_Lean_stringToMessageData(v___y_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_907_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
if (v_isMeta_821_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18));
v___y_893_ = v___x_913_;
v___y_894_ = v___x_914_;
goto v___jp_892_;
}
else
{
lean_object* v___x_915_; 
v___x_915_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19));
v___y_893_ = v___x_913_;
v___y_894_ = v___x_915_;
goto v___jp_892_;
}
}
}
v___jp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___y_888_);
lean_ctor_set(v___x_890_, 1, v___y_889_);
v___x_891_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(v_cls_884_, v___x_890_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_dec_ref(v___x_891_);
v___y_841_ = v___y_826_;
v___y_842_ = v___y_828_;
goto v___jp_840_;
}
else
{
lean_dec_ref(v_entry_836_);
return v___x_891_;
}
}
v___jp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_895_ = l_Lean_stringToMessageData(v___y_894_);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___y_893_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_MessageData_ofName(v_mod_820_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_Name_isAnonymous(v_hint_822_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12);
v___x_903_ = l_Lean_MessageData_ofName(v_hint_822_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___y_888_ = v___x_900_;
v___y_889_ = v___x_904_;
goto v___jp_887_;
}
else
{
lean_object* v___x_905_; 
lean_dec(v_hint_822_);
v___x_905_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13);
v___y_888_ = v___x_900_;
v___y_889_ = v___x_905_;
goto v___jp_887_;
}
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_entry_836_);
lean_dec(v_hint_822_);
lean_dec(v_mod_820_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
v___jp_840_:
{
lean_object* v___x_843_; lean_object* v_toEnvExtension_844_; lean_object* v_env_845_; lean_object* v_nextMacroScope_846_; lean_object* v_ngen_847_; lean_object* v_auxDeclNGen_848_; lean_object* v_traceState_849_; lean_object* v_messages_850_; lean_object* v_infoState_851_; lean_object* v_snapshotTasks_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_880_; 
v___x_843_ = lean_st_ref_take(v___y_842_);
v_toEnvExtension_844_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_toEnvExtension_844_);
v_env_845_ = lean_ctor_get(v___x_843_, 0);
v_nextMacroScope_846_ = lean_ctor_get(v___x_843_, 1);
v_ngen_847_ = lean_ctor_get(v___x_843_, 2);
v_auxDeclNGen_848_ = lean_ctor_get(v___x_843_, 3);
v_traceState_849_ = lean_ctor_get(v___x_843_, 4);
v_messages_850_ = lean_ctor_get(v___x_843_, 6);
v_infoState_851_ = lean_ctor_get(v___x_843_, 7);
v_snapshotTasks_852_ = lean_ctor_get(v___x_843_, 8);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v___x_843_, 5);
lean_dec(v_unused_881_);
v___x_854_ = v___x_843_;
v_isShared_855_ = v_isSharedCheck_880_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snapshotTasks_852_);
lean_inc(v_infoState_851_);
lean_inc(v_messages_850_);
lean_inc(v_traceState_849_);
lean_inc(v_auxDeclNGen_848_);
lean_inc(v_ngen_847_);
lean_inc(v_nextMacroScope_846_);
lean_inc(v_env_845_);
lean_dec(v___x_843_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_880_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_asyncMode_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v_asyncMode_856_ = lean_ctor_get(v_toEnvExtension_844_, 2);
lean_inc(v_asyncMode_856_);
lean_dec_ref(v_toEnvExtension_844_);
v___x_857_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_837_, v_env_845_, v_entry_836_, v_asyncMode_856_, v___x_839_);
lean_dec(v_asyncMode_856_);
v___x_858_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 5, v___x_858_);
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_860_ = v___x_854_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_846_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_847_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_traceState_849_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_messages_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_infoState_851_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_snapshotTasks_852_);
v___x_860_ = v_reuseFailAlloc_879_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v_zetaDeltaFVarIds_864_; lean_object* v_postponed_865_; lean_object* v_diag_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v___x_861_ = lean_st_ref_set(v___y_842_, v___x_860_);
v___x_862_ = lean_st_ref_take(v___y_841_);
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
v___x_870_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6);
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
v___x_873_ = lean_st_ref_set(v___y_841_, v___x_872_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___boxed(lean_object* v_mod_920_, lean_object* v_isMeta_921_, lean_object* v_hint_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v_isMeta_boxed_930_; lean_object* v_res_931_; 
v_isMeta_boxed_930_ = lean_unbox(v_isMeta_921_);
v_res_931_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(v_mod_920_, v_isMeta_boxed_930_, v_hint_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(lean_object* v___x_932_, lean_object* v_declName_933_, lean_object* v_as_934_, size_t v_sz_935_, size_t v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_936_, v_sz_935_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
lean_dec(v_declName_933_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_937_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; lean_object* v_modules_948_; lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v_toImport_952_; lean_object* v_module_953_; uint8_t v___x_954_; lean_object* v___x_955_; 
v___x_947_ = l_Lean_Environment_header(v___x_932_);
v_modules_948_ = lean_ctor_get(v___x_947_, 3);
lean_inc_ref(v_modules_948_);
lean_dec_ref(v___x_947_);
v___x_949_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_950_ = lean_array_uget_borrowed(v_as_934_, v_i_936_);
v___x_951_ = lean_array_get(v___x_949_, v_modules_948_, v_a_950_);
lean_dec_ref(v_modules_948_);
v_toImport_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_toImport_952_);
lean_dec(v___x_951_);
v_module_953_ = lean_ctor_get(v_toImport_952_, 0);
lean_inc(v_module_953_);
lean_dec_ref(v_toImport_952_);
v___x_954_ = 0;
lean_inc(v_declName_933_);
v___x_955_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(v_module_953_, v___x_954_, v_declName_933_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; 
lean_dec_ref(v___x_955_);
v___x_956_ = lean_box(0);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_936_, v___x_957_);
v_i_936_ = v___x_958_;
v_b_937_ = v___x_956_;
goto _start;
}
else
{
lean_dec(v_declName_933_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10___boxed(lean_object* v___x_960_, lean_object* v_declName_961_, lean_object* v_as_962_, lean_object* v_sz_963_, lean_object* v_i_964_, lean_object* v_b_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
size_t v_sz_boxed_973_; size_t v_i_boxed_974_; lean_object* v_res_975_; 
v_sz_boxed_973_ = lean_unbox_usize(v_sz_963_);
lean_dec(v_sz_963_);
v_i_boxed_974_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_res_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(v___x_960_, v_declName_961_, v_as_962_, v_sz_boxed_973_, v_i_boxed_974_, v_b_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_as_962_);
lean_dec_ref(v___x_960_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(lean_object* v_a_976_, lean_object* v_x_977_){
_start:
{
if (lean_obj_tag(v_x_977_) == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_box(0);
return v___x_978_;
}
else
{
lean_object* v_key_979_; lean_object* v_value_980_; lean_object* v_tail_981_; uint8_t v___x_982_; 
v_key_979_ = lean_ctor_get(v_x_977_, 0);
v_value_980_ = lean_ctor_get(v_x_977_, 1);
v_tail_981_ = lean_ctor_get(v_x_977_, 2);
v___x_982_ = lean_name_eq(v_key_979_, v_a_976_);
if (v___x_982_ == 0)
{
v_x_977_ = v_tail_981_;
goto _start;
}
else
{
lean_object* v___x_984_; 
lean_inc(v_value_980_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v_value_980_);
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg___boxed(lean_object* v_a_985_, lean_object* v_x_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(v_a_985_, v_x_986_);
lean_dec(v_x_986_);
lean_dec(v_a_985_);
return v_res_987_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_988_; uint64_t v___x_989_; 
v___x_988_ = lean_unsigned_to_nat(1723u);
v___x_989_ = lean_uint64_of_nat(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(lean_object* v_m_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_buckets_992_; lean_object* v___x_993_; uint64_t v___y_995_; 
v_buckets_992_ = lean_ctor_get(v_m_990_, 1);
v___x_993_ = lean_array_get_size(v_buckets_992_);
if (lean_obj_tag(v_a_991_) == 0)
{
uint64_t v___x_1009_; 
v___x_1009_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0);
v___y_995_ = v___x_1009_;
goto v___jp_994_;
}
else
{
uint64_t v_hash_1010_; 
v_hash_1010_ = lean_ctor_get_uint64(v_a_991_, sizeof(void*)*2);
v___y_995_ = v_hash_1010_;
goto v___jp_994_;
}
v___jp_994_:
{
uint64_t v___x_996_; uint64_t v___x_997_; uint64_t v_fold_998_; uint64_t v___x_999_; uint64_t v___x_1000_; uint64_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_996_ = 32ULL;
v___x_997_ = lean_uint64_shift_right(v___y_995_, v___x_996_);
v_fold_998_ = lean_uint64_xor(v___y_995_, v___x_997_);
v___x_999_ = 16ULL;
v___x_1000_ = lean_uint64_shift_right(v_fold_998_, v___x_999_);
v___x_1001_ = lean_uint64_xor(v_fold_998_, v___x_1000_);
v___x_1002_ = lean_uint64_to_usize(v___x_1001_);
v___x_1003_ = lean_usize_of_nat(v___x_993_);
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_sub(v___x_1003_, v___x_1004_);
v___x_1006_ = lean_usize_land(v___x_1002_, v___x_1005_);
v___x_1007_ = lean_array_uget_borrowed(v_buckets_992_, v___x_1006_);
v___x_1008_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(v_a_991_, v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_m_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(v_m_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_m_1011_);
return v_res_1013_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1));
v___x_1017_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0));
v___x_1018_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_declName_1021_, uint8_t v_isMeta_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_env_1034_; lean_object* v___y_1036_; lean_object* v___x_1049_; 
v___x_1030_ = lean_st_ref_get(v___y_1028_);
v_env_1034_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_env_1034_);
lean_dec(v___x_1030_);
v___x_1049_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1034_, v_declName_1021_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_dec_ref(v_env_1034_);
lean_dec(v_declName_1021_);
goto v___jp_1031_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1051_; lean_object* v_modules_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_val_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_val_1050_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = l_Lean_Environment_header(v_env_1034_);
v_modules_1052_ = lean_ctor_get(v___x_1051_, 3);
lean_inc_ref(v_modules_1052_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = lean_array_get_size(v_modules_1052_);
v___x_1054_ = lean_nat_dec_lt(v_val_1050_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec_ref(v_modules_1052_);
lean_dec(v_val_1050_);
lean_dec_ref(v_env_1034_);
lean_dec(v_declName_1021_);
goto v___jp_1031_;
}
else
{
lean_object* v___x_1055_; lean_object* v_env_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___y_1060_; 
v___x_1055_ = lean_st_ref_get(v___y_1028_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2);
v___x_1058_ = lean_array_fget(v_modules_1052_, v_val_1050_);
lean_dec(v_val_1050_);
lean_dec_ref(v_modules_1052_);
if (v_isMeta_1022_ == 0)
{
lean_dec_ref(v_env_1056_);
v___y_1060_ = v_isMeta_1022_;
goto v___jp_1059_;
}
else
{
uint8_t v___x_1071_; 
lean_inc(v_declName_1021_);
v___x_1071_ = l_Lean_isMarkedMeta(v_env_1056_, v_declName_1021_);
if (v___x_1071_ == 0)
{
v___y_1060_ = v_isMeta_1022_;
goto v___jp_1059_;
}
else
{
uint8_t v___x_1072_; 
v___x_1072_ = 0;
v___y_1060_ = v___x_1072_;
goto v___jp_1059_;
}
}
v___jp_1059_:
{
lean_object* v_toImport_1061_; lean_object* v_module_1062_; lean_object* v___x_1063_; 
v_toImport_1061_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_ref(v_toImport_1061_);
lean_dec(v___x_1058_);
v_module_1062_ = lean_ctor_get(v_toImport_1061_, 0);
lean_inc(v_module_1062_);
lean_dec_ref(v_toImport_1061_);
lean_inc(v_declName_1021_);
v___x_1063_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(v_module_1062_, v___y_1060_, v_declName_1021_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v___x_1063_);
v___x_1064_ = l_Lean_indirectModUseExt;
v___x_1065_ = lean_box(1);
v___x_1066_ = lean_box(0);
lean_inc_ref(v_env_1034_);
v___x_1067_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1057_, v___x_1064_, v_env_1034_, v___x_1065_, v___x_1066_);
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(v___x_1067_, v_declName_1021_);
lean_dec(v___x_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3));
v___y_1036_ = v___x_1069_;
goto v___jp_1035_;
}
else
{
lean_object* v_val_1070_; 
v_val_1070_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v___x_1068_);
v___y_1036_ = v_val_1070_;
goto v___jp_1035_;
}
}
else
{
lean_dec_ref(v_env_1034_);
lean_dec(v_declName_1021_);
return v___x_1063_;
}
}
}
}
v___jp_1031_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
v___jp_1035_:
{
lean_object* v___x_1037_; size_t v_sz_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1037_ = lean_box(0);
v_sz_1038_ = lean_array_size(v___y_1036_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(v_env_1034_, v_declName_1021_, v___y_1036_, v_sz_1038_, v___x_1039_, v___x_1037_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_env_1034_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v___x_1040_, 0);
lean_dec(v_unused_1048_);
v___x_1042_ = v___x_1040_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v___x_1040_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1037_);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1037_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
else
{
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_declName_1073_, lean_object* v_isMeta_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
uint8_t v_isMeta_boxed_1082_; lean_object* v_res_1083_; 
v_isMeta_boxed_1082_ = lean_unbox(v_isMeta_1074_);
v_res_1083_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_declName_1073_, v_isMeta_boxed_1082_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(lean_object* v_as_x27_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
if (lean_obj_tag(v_as_x27_1084_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_b_1085_);
return v___x_1093_;
}
else
{
lean_object* v_head_1094_; lean_object* v_tail_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; 
v_head_1094_ = lean_ctor_get(v_as_x27_1084_, 0);
lean_inc(v_head_1094_);
v_tail_1095_ = lean_ctor_get(v_as_x27_1084_, 1);
lean_inc(v_tail_1095_);
lean_dec_ref(v_as_x27_1084_);
v___x_1096_ = 1;
v___x_1097_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_head_1094_, v___x_1096_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; 
lean_dec_ref(v___x_1097_);
v___x_1098_ = lean_box(0);
v_as_x27_1084_ = v_tail_1095_;
v_b_1085_ = v___x_1098_;
goto _start;
}
else
{
lean_dec(v_tail_1095_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg___boxed(lean_object* v_as_x27_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(v_as_x27_1100_, v_b_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1110_, lean_object* v_currNamespace_1111_, lean_object* v_openDecls_1112_, lean_object* v_n_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = l_Lean_ResolveName_resolveNamespace(v_env_1110_, v_currNamespace_1111_, v_openDecls_1112_, v_n_1113_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1118_, lean_object* v_currNamespace_1119_, lean_object* v_openDecls_1120_, lean_object* v_n_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1118_, v_currNamespace_1119_, v_openDecls_1120_, v_n_1121_, v___y_1122_, v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_as_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
if (lean_obj_tag(v_as_1125_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v_head_1135_; lean_object* v_tail_1136_; lean_object* v_fst_1137_; lean_object* v_snd_1138_; lean_object* v___x_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1152_; 
v_head_1135_ = lean_ctor_get(v_as_1125_, 0);
lean_inc(v_head_1135_);
v_tail_1136_ = lean_ctor_get(v_as_1125_, 1);
lean_inc(v_tail_1136_);
lean_dec_ref(v_as_1125_);
v_fst_1137_ = lean_ctor_get(v_head_1135_, 0);
lean_inc(v_fst_1137_);
v_snd_1138_ = lean_ctor_get(v_head_1135_, 1);
lean_inc(v_snd_1138_);
lean_dec(v_head_1135_);
lean_inc(v_fst_1137_);
v___x_1139_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_1137_, v___y_1130_);
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_unbox(v_a_1140_);
lean_dec(v_a_1140_);
if (v___x_1144_ == 0)
{
lean_del_object(v___x_1142_);
lean_dec(v_snd_1138_);
lean_dec(v_fst_1137_);
v_as_1125_ = v_tail_1136_;
goto _start;
}
else
{
lean_object* v___x_1147_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 3);
lean_ctor_set(v___x_1142_, 0, v_snd_1138_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_snd_1138_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = l_Lean_MessageData_ofFormat(v___x_1147_);
v___x_1149_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(v_fst_1137_, v___x_1148_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_dec_ref(v___x_1149_);
v_as_1125_ = v_tail_1136_;
goto _start;
}
else
{
lean_dec(v_tail_1136_);
return v___x_1149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_as_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_as_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_currNamespace_1162_);
lean_ctor_set(v___x_1165_, 1, v___y_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1166_, v___y_1167_, v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1170_, lean_object* v_options_1171_, lean_object* v_currNamespace_1172_, lean_object* v_openDecls_1173_, lean_object* v_n_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_ResolveName_resolveGlobalName(v_env_1170_, v_options_1171_, v_currNamespace_1172_, v_openDecls_1173_, v_n_1174_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1179_, lean_object* v_options_1180_, lean_object* v_currNamespace_1181_, lean_object* v_openDecls_1182_, lean_object* v_n_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1179_, v_options_1180_, v_currNamespace_1181_, v_openDecls_1182_, v_n_1183_, v___y_1184_, v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v_options_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v_env_1197_; lean_object* v_options_1198_; lean_object* v_currRecDepth_1199_; lean_object* v_maxRecDepth_1200_; lean_object* v_ref_1201_; lean_object* v_currNamespace_1202_; lean_object* v_openDecls_1203_; lean_object* v_quotContext_1204_; lean_object* v_currMacroScope_1205_; lean_object* v___x_1206_; lean_object* v_nextMacroScope_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v_methods_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1196_ = lean_st_ref_get(v___y_1194_);
v_env_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_env_1197_);
lean_dec(v___x_1196_);
v_options_1198_ = lean_ctor_get(v___y_1193_, 2);
v_currRecDepth_1199_ = lean_ctor_get(v___y_1193_, 3);
v_maxRecDepth_1200_ = lean_ctor_get(v___y_1193_, 4);
v_ref_1201_ = lean_ctor_get(v___y_1193_, 5);
v_currNamespace_1202_ = lean_ctor_get(v___y_1193_, 6);
v_openDecls_1203_ = lean_ctor_get(v___y_1193_, 7);
v_quotContext_1204_ = lean_ctor_get(v___y_1193_, 10);
v_currMacroScope_1205_ = lean_ctor_get(v___y_1193_, 11);
v___x_1206_ = lean_st_ref_get(v___y_1194_);
v_nextMacroScope_1207_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_nextMacroScope_1207_);
lean_dec(v___x_1206_);
lean_inc_ref(v_env_1197_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1208_, 0, v_env_1197_);
lean_inc_ref(v_env_1197_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1209_, 0, v_env_1197_);
lean_inc(v_openDecls_1203_);
lean_inc(v_currNamespace_1202_);
lean_inc_ref(v_env_1197_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1210_, 0, v_env_1197_);
lean_closure_set(v___f_1210_, 1, v_currNamespace_1202_);
lean_closure_set(v___f_1210_, 2, v_openDecls_1203_);
lean_inc(v_currNamespace_1202_);
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1211_, 0, v_currNamespace_1202_);
lean_inc(v_openDecls_1203_);
lean_inc(v_currNamespace_1202_);
lean_inc_ref(v_options_1198_);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1212_, 0, v_env_1197_);
lean_closure_set(v___f_1212_, 1, v_options_1198_);
lean_closure_set(v___f_1212_, 2, v_currNamespace_1202_);
lean_closure_set(v___f_1212_, 3, v_openDecls_1203_);
v_methods_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1213_, 0, v___f_1208_);
lean_ctor_set(v_methods_1213_, 1, v___f_1211_);
lean_ctor_set(v_methods_1213_, 2, v___f_1209_);
lean_ctor_set(v_methods_1213_, 3, v___f_1210_);
lean_ctor_set(v_methods_1213_, 4, v___f_1212_);
lean_inc(v_ref_1201_);
lean_inc(v_maxRecDepth_1200_);
lean_inc(v_currRecDepth_1199_);
lean_inc(v_currMacroScope_1205_);
lean_inc(v_quotContext_1204_);
v___x_1214_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1214_, 0, v_methods_1213_);
lean_ctor_set(v___x_1214_, 1, v_quotContext_1204_);
lean_ctor_set(v___x_1214_, 2, v_currMacroScope_1205_);
lean_ctor_set(v___x_1214_, 3, v_currRecDepth_1199_);
lean_ctor_set(v___x_1214_, 4, v_maxRecDepth_1200_);
lean_ctor_set(v___x_1214_, 5, v_ref_1201_);
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1216_, 0, v_nextMacroScope_1207_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
v___x_1217_ = lean_apply_2(v_x_1188_, v___x_1214_, v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v_macroScope_1220_; lean_object* v_traceMsgs_1221_; lean_object* v_expandedMacroDecls_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_a_1218_);
v_a_1219_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1217_);
v_macroScope_1220_ = lean_ctor_get(v_a_1218_, 0);
lean_inc(v_macroScope_1220_);
v_traceMsgs_1221_ = lean_ctor_get(v_a_1218_, 1);
lean_inc(v_traceMsgs_1221_);
v_expandedMacroDecls_1222_ = lean_ctor_get(v_a_1218_, 2);
lean_inc(v_expandedMacroDecls_1222_);
lean_dec(v_a_1218_);
v___x_1223_ = lean_box(0);
v___x_1224_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(v_expandedMacroDecls_1222_, v___x_1223_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; lean_object* v_env_1226_; lean_object* v_ngen_1227_; lean_object* v_auxDeclNGen_1228_; lean_object* v_traceState_1229_; lean_object* v_cache_1230_; lean_object* v_messages_1231_; lean_object* v_infoState_1232_; lean_object* v_snapshotTasks_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v___x_1224_);
v___x_1225_ = lean_st_ref_take(v___y_1194_);
v_env_1226_ = lean_ctor_get(v___x_1225_, 0);
v_ngen_1227_ = lean_ctor_get(v___x_1225_, 2);
v_auxDeclNGen_1228_ = lean_ctor_get(v___x_1225_, 3);
v_traceState_1229_ = lean_ctor_get(v___x_1225_, 4);
v_cache_1230_ = lean_ctor_get(v___x_1225_, 5);
v_messages_1231_ = lean_ctor_get(v___x_1225_, 6);
v_infoState_1232_ = lean_ctor_get(v___x_1225_, 7);
v_snapshotTasks_1233_ = lean_ctor_get(v___x_1225_, 8);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1225_, 1);
lean_dec(v_unused_1260_);
v___x_1235_ = v___x_1225_;
v_isShared_1236_ = v_isSharedCheck_1259_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snapshotTasks_1233_);
lean_inc(v_infoState_1232_);
lean_inc(v_messages_1231_);
lean_inc(v_cache_1230_);
lean_inc(v_traceState_1229_);
lean_inc(v_auxDeclNGen_1228_);
lean_inc(v_ngen_1227_);
lean_inc(v_env_1226_);
lean_dec(v___x_1225_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1259_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_macroScope_1220_);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_env_1226_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_macroScope_1220_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_ngen_1227_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_auxDeclNGen_1228_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_traceState_1229_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v_cache_1230_);
lean_ctor_set(v_reuseFailAlloc_1258_, 6, v_messages_1231_);
lean_ctor_set(v_reuseFailAlloc_1258_, 7, v_infoState_1232_);
lean_ctor_set(v_reuseFailAlloc_1258_, 8, v_snapshotTasks_1233_);
v___x_1238_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_st_ref_set(v___y_1194_, v___x_1238_);
v___x_1240_ = l_List_reverse___redArg(v_traceMsgs_1221_);
v___x_1241_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v___x_1240_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec_ref(v___y_1193_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1249_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_a_1219_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1219_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1219_);
v_a_1250_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1241_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1241_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_traceMsgs_1221_);
lean_dec(v_macroScope_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v___y_1193_);
v_a_1261_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1224_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1224_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; 
v_a_1269_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v___x_1217_);
if (lean_obj_tag(v_a_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v_a_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_a_1270_ = lean_ctor_get(v_a_1269_, 0);
lean_inc(v_a_1270_);
v_a_1271_ = lean_ctor_get(v_a_1269_, 1);
lean_inc_ref(v_a_1271_);
lean_dec_ref(v_a_1269_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1273_ = lean_string_dec_eq(v_a_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1271_);
v___x_1275_ = l_Lean_MessageData_ofFormat(v___x_1274_);
v___x_1276_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1270_, v___x_1275_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v_a_1270_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; 
lean_dec_ref(v_a_1271_);
lean_dec_ref(v___y_1193_);
v___x_1277_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(v_a_1270_);
return v___x_1277_;
}
}
else
{
lean_object* v___x_1278_; 
lean_dec_ref(v___y_1193_);
v___x_1278_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1291_, size_t v_i_1292_, lean_object* v_bs_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_usize_dec_lt(v_i_1292_, v_sz_1291_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_bs_1293_);
return v___x_1295_;
}
else
{
lean_object* v_v_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_v_1296_ = lean_array_uget(v_bs_1293_, v_i_1292_);
v___x_1297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1296_);
v___x_1298_ = l_Lean_Syntax_isOfKind(v_v_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v_v_1296_);
lean_dec_ref(v_bs_1293_);
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = l_Lean_Syntax_getArg(v_v_1296_, v___x_1300_);
v___x_1302_ = l_Lean_Syntax_isOfKind(v___x_1301_, v___x_1297_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec(v_v_1296_);
lean_dec_ref(v_bs_1293_);
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; lean_object* v_bs_x27_1305_; lean_object* v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = lean_unsigned_to_nat(3u);
v_bs_x27_1305_ = lean_array_uset(v_bs_1293_, v_i_1292_, v___x_1300_);
v___x_1306_ = l_Lean_Syntax_getArg(v_v_1296_, v___x_1304_);
lean_dec(v_v_1296_);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_add(v_i_1292_, v___x_1307_);
v___x_1309_ = lean_array_uset(v_bs_x27_1305_, v_i_1292_, v___x_1306_);
v_i_1292_ = v___x_1308_;
v_bs_1293_ = v___x_1309_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1311_, lean_object* v_i_1312_, lean_object* v_bs_1313_){
_start:
{
size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1311_);
lean_dec(v_sz_1311_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1314_, v_i_boxed_1315_, v_bs_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1329_, size_t v_i_1330_, lean_object* v_bs_1331_){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_usize_dec_lt(v_i_1330_, v_sz_1329_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_bs_1331_);
return v___x_1333_;
}
else
{
lean_object* v_v_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_v_1334_ = lean_array_uget(v_bs_1331_, v_i_1330_);
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1334_);
v___x_1336_ = l_Lean_Syntax_isOfKind(v_v_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v_v_1334_);
lean_dec_ref(v_bs_1331_);
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1338_ = lean_unsigned_to_nat(1u);
v___x_1339_ = l_Lean_Syntax_getArg(v_v_1334_, v___x_1338_);
v___x_1340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1341_ = l_Lean_Syntax_isOfKind(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec(v_v_1334_);
lean_dec_ref(v_bs_1331_);
v___x_1342_ = lean_box(0);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_bs_x27_1345_; lean_object* v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1343_ = lean_unsigned_to_nat(3u);
v___x_1344_ = lean_unsigned_to_nat(0u);
v_bs_x27_1345_ = lean_array_uset(v_bs_1331_, v_i_1330_, v___x_1344_);
v___x_1346_ = l_Lean_Syntax_getArg(v_v_1334_, v___x_1343_);
lean_dec(v_v_1334_);
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1330_, v___x_1347_);
v___x_1349_ = lean_array_uset(v_bs_x27_1345_, v_i_1330_, v___x_1346_);
v_i_1330_ = v___x_1348_;
v_bs_1331_ = v___x_1349_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1351_, lean_object* v_i_1352_, lean_object* v_bs_1353_){
_start:
{
size_t v_sz_boxed_1354_; size_t v_i_boxed_1355_; lean_object* v_res_1356_; 
v_sz_boxed_1354_ = lean_unbox_usize(v_sz_1351_);
lean_dec(v_sz_1351_);
v_i_boxed_1355_ = lean_unbox_usize(v_i_1352_);
lean_dec(v_i_1352_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1354_, v_i_boxed_1355_, v_bs_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_bs_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_bs_1365_);
return v___x_1367_;
}
else
{
lean_object* v_v_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_v_1368_ = lean_array_uget(v_bs_1365_, v_i_1364_);
v___x_1369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1368_);
v___x_1370_ = l_Lean_Syntax_isOfKind(v_v_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v_v_1368_);
lean_dec_ref(v_bs_1365_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v_bs_x27_1373_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1372_ = lean_unsigned_to_nat(0u);
v_bs_x27_1373_ = lean_array_uset(v_bs_1365_, v_i_1364_, v___x_1372_);
v___x_1380_ = l_Lean_Syntax_getArg(v_v_1368_, v___x_1372_);
lean_dec(v_v_1368_);
v___x_1381_ = l_Lean_Syntax_isNone(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(2u);
v___x_1383_ = l_Lean_Syntax_matchesNull(v___x_1380_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref(v_bs_x27_1373_);
v___x_1384_ = lean_box(0);
return v___x_1384_;
}
else
{
goto v___jp_1374_;
}
}
else
{
lean_dec(v___x_1380_);
goto v___jp_1374_;
}
v___jp_1374_:
{
lean_object* v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1364_, v___x_1376_);
v___x_1378_ = lean_array_uset(v_bs_x27_1373_, v_i_1364_, v___x_1375_);
v_i_1364_ = v___x_1377_;
v_bs_1365_ = v___x_1378_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_bs_1387_){
_start:
{
size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1388_, v_i_boxed_1389_, v_bs_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_bs_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_bs_1393_);
return v___x_1395_;
}
else
{
lean_object* v_v_1396_; lean_object* v___x_1397_; lean_object* v_bs_x27_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v_v_1396_ = lean_array_uget(v_bs_1393_, v_i_1392_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v_bs_x27_1398_ = lean_array_uset(v_bs_1393_, v_i_1392_, v___x_1397_);
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_add(v_i_1392_, v___x_1399_);
v___x_1401_ = lean_array_uset(v_bs_x27_1398_, v_i_1392_, v_v_1396_);
v_i_1392_ = v___x_1400_;
v_bs_1393_ = v___x_1401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1403_, lean_object* v_i_1404_, lean_object* v_bs_1405_){
_start:
{
size_t v_sz_boxed_1406_; size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_sz_boxed_1406_ = lean_unbox_usize(v_sz_1403_);
lean_dec(v_sz_1403_);
v_i_boxed_1407_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1406_, v_i_boxed_1407_, v_bs_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1410_, v___y_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1414_, v_x_1415_, v___y_1416_, v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v_x_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1422_, lean_object* v_as_x27_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
if (lean_obj_tag(v_as_x27_1423_) == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_stx_1422_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1424_);
return v___x_1432_;
}
else
{
lean_object* v_head_1433_; lean_object* v_tail_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_b_1424_);
v_head_1433_ = lean_ctor_get(v_as_x27_1423_, 0);
v_tail_1434_ = lean_ctor_get(v_as_x27_1423_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_as_x27_1423_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1436_ = v_as_x27_1423_;
v_isShared_1437_ = v_isSharedCheck_1476_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_tail_1434_);
lean_inc(v_head_1433_);
lean_dec(v_as_x27_1423_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1476_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_value_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_value_1438_ = lean_ctor_get(v_head_1433_, 1);
lean_inc(v_value_1438_);
lean_dec(v_head_1433_);
v___x_1439_ = lean_box(0);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v_stx_1422_);
v___x_1440_ = lean_apply_8(v_value_1438_, v_stx_1422_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, lean_box(0));
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_tail_1434_);
lean_dec(v_stx_1422_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1452_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1452_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_a_1441_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 0);
lean_ctor_set(v___x_1436_, 1, v___x_1439_);
lean_ctor_set(v___x_1436_, 0, v___x_1445_);
v___x_1447_ = v___x_1436_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1439_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1447_);
v___x_1449_ = v___x_1443_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1475_; 
lean_del_object(v___x_1436_);
v_a_1453_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1455_ = v___x_1440_;
v_isShared_1456_ = v_isSharedCheck_1475_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1440_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1475_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___y_1460_; uint8_t v___x_1473_; 
v___x_1457_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1458_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1473_ = l_Lean_Exception_isInterrupt(v_a_1453_);
if (v___x_1473_ == 0)
{
uint8_t v___x_1474_; 
lean_inc(v_a_1453_);
v___x_1474_ = l_Lean_Exception_isRuntime(v_a_1453_);
v___y_1460_ = v___x_1474_;
goto v___jp_1459_;
}
else
{
v___y_1460_ = v___x_1473_;
goto v___jp_1459_;
}
v___jp_1459_:
{
if (v___y_1460_ == 0)
{
if (lean_obj_tag(v_a_1453_) == 0)
{
lean_object* v___x_1462_; 
lean_dec(v_tail_1434_);
lean_dec(v_stx_1422_);
if (v_isShared_1456_ == 0)
{
v___x_1462_ = v___x_1455_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1453_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v_id_1464_; uint8_t v___x_1465_; 
v_id_1464_ = lean_ctor_get(v_a_1453_, 0);
v___x_1465_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1458_, v_id_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1467_; 
lean_dec(v_tail_1434_);
lean_dec(v_stx_1422_);
if (v_isShared_1456_ == 0)
{
v___x_1467_ = v___x_1455_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1453_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_dec_ref(v_a_1453_);
lean_del_object(v___x_1455_);
v_as_x27_1423_ = v_tail_1434_;
v_b_1424_ = v___x_1457_;
goto _start;
}
}
}
else
{
lean_object* v___x_1471_; 
lean_dec(v_tail_1434_);
lean_dec(v_stx_1422_);
if (v_isShared_1456_ == 0)
{
v___x_1471_ = v___x_1455_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1453_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1477_, lean_object* v_as_x27_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1477_, v_as_x27_1478_, v_b_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1490_, lean_object* v_rhs_x3f_1491_, lean_object* v_otherwise_x3f_1492_, lean_object* v_body_x3f_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
uint8_t v___y_1502_; lean_object* v___y_1503_; uint8_t v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v_body_1512_; lean_object* v___y_1532_; lean_object* v_otherwise_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v_rhs_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; 
if (lean_obj_tag(v_rhs_x3f_1491_) == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v_rhs_1545_ = v___x_1556_;
v___y_1546_ = v_a_1494_;
v___y_1547_ = v_a_1495_;
v___y_1548_ = v_a_1496_;
v___y_1549_ = v_a_1497_;
v___y_1550_ = v_a_1498_;
v___y_1551_ = v_a_1499_;
goto v___jp_1544_;
}
else
{
lean_object* v_val_1557_; lean_object* v___x_1558_; 
v_val_1557_ = lean_ctor_get(v_rhs_x3f_1491_, 0);
lean_inc(v_val_1557_);
lean_dec_ref(v_rhs_x3f_1491_);
v___x_1558_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1557_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1558_);
v_rhs_1545_ = v_a_1559_;
v___y_1546_ = v_a_1494_;
v___y_1547_ = v_a_1495_;
v___y_1548_ = v_a_1496_;
v___y_1549_ = v_a_1497_;
v___y_1550_ = v_a_1498_;
v___y_1551_ = v_a_1499_;
goto v___jp_1544_;
}
else
{
lean_dec(v_body_x3f_1493_);
lean_dec(v_otherwise_x3f_1492_);
lean_dec_ref(v_reassigned_1490_);
return v___x_1558_;
}
}
v___jp_1501_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1507_, 0, v___y_1503_);
lean_ctor_set(v___x_1507_, 1, v___y_1506_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*2, v___y_1504_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*2 + 1, v___y_1505_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*2 + 2, v___y_1502_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
v___jp_1509_:
{
lean_object* v___x_1513_; lean_object* v_info_1514_; uint8_t v_breaks_1515_; uint8_t v_continues_1516_; uint8_t v_returnsEarly_1517_; lean_object* v_numRegularExits_1518_; lean_object* v_reassigns_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1513_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1512_, v___y_1510_);
v_info_1514_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1511_, v___x_1513_);
v_breaks_1515_ = lean_ctor_get_uint8(v_info_1514_, sizeof(void*)*2);
v_continues_1516_ = lean_ctor_get_uint8(v_info_1514_, sizeof(void*)*2 + 1);
v_returnsEarly_1517_ = lean_ctor_get_uint8(v_info_1514_, sizeof(void*)*2 + 2);
v_numRegularExits_1518_ = lean_ctor_get(v_info_1514_, 0);
lean_inc(v_numRegularExits_1518_);
v_reassigns_1519_ = lean_ctor_get(v_info_1514_, 1);
lean_inc(v_reassigns_1519_);
lean_dec_ref(v_info_1514_);
v_sz_1520_ = lean_array_size(v_reassigned_1490_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1520_, v___x_1521_, v_reassigned_1490_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_array_get_size(v___x_1522_);
v___x_1525_ = lean_nat_dec_lt(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec_ref(v___x_1522_);
v___y_1502_ = v_returnsEarly_1517_;
v___y_1503_ = v_numRegularExits_1518_;
v___y_1504_ = v_breaks_1515_;
v___y_1505_ = v_continues_1516_;
v___y_1506_ = v_reassigns_1519_;
goto v___jp_1501_;
}
else
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_le(v___x_1524_, v___x_1524_);
if (v___x_1526_ == 0)
{
if (v___x_1525_ == 0)
{
lean_dec_ref(v___x_1522_);
v___y_1502_ = v_returnsEarly_1517_;
v___y_1503_ = v_numRegularExits_1518_;
v___y_1504_ = v_breaks_1515_;
v___y_1505_ = v_continues_1516_;
v___y_1506_ = v_reassigns_1519_;
goto v___jp_1501_;
}
else
{
size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_usize_of_nat(v___x_1524_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1522_, v___x_1521_, v___x_1527_, v_reassigns_1519_);
lean_dec_ref(v___x_1522_);
v___y_1502_ = v_returnsEarly_1517_;
v___y_1503_ = v_numRegularExits_1518_;
v___y_1504_ = v_breaks_1515_;
v___y_1505_ = v_continues_1516_;
v___y_1506_ = v___x_1528_;
goto v___jp_1501_;
}
}
else
{
size_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_usize_of_nat(v___x_1524_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1522_, v___x_1521_, v___x_1529_, v_reassigns_1519_);
lean_dec_ref(v___x_1522_);
v___y_1502_ = v_returnsEarly_1517_;
v___y_1503_ = v_numRegularExits_1518_;
v___y_1504_ = v_breaks_1515_;
v___y_1505_ = v_continues_1516_;
v___y_1506_ = v___x_1530_;
goto v___jp_1501_;
}
}
}
v___jp_1531_:
{
if (lean_obj_tag(v_body_x3f_1493_) == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___y_1510_ = v_otherwise_1533_;
v___y_1511_ = v___y_1532_;
v_body_1512_ = v___x_1540_;
goto v___jp_1509_;
}
else
{
lean_object* v_val_1541_; lean_object* v___x_1542_; 
v_val_1541_ = lean_ctor_get(v_body_x3f_1493_, 0);
lean_inc(v_val_1541_);
lean_dec_ref(v_body_x3f_1493_);
v___x_1542_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1541_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___y_1510_ = v_otherwise_1533_;
v___y_1511_ = v___y_1532_;
v_body_1512_ = v_a_1543_;
goto v___jp_1509_;
}
else
{
lean_dec_ref(v_otherwise_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_reassigned_1490_);
return v___x_1542_;
}
}
}
v___jp_1544_:
{
if (lean_obj_tag(v_otherwise_x3f_1492_) == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___y_1532_ = v_rhs_1545_;
v_otherwise_1533_ = v___x_1552_;
v___y_1534_ = v___y_1546_;
v___y_1535_ = v___y_1547_;
v___y_1536_ = v___y_1548_;
v___y_1537_ = v___y_1549_;
v___y_1538_ = v___y_1550_;
v___y_1539_ = v___y_1551_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1554_; 
v_val_1553_ = lean_ctor_get(v_otherwise_x3f_1492_, 0);
lean_inc(v_val_1553_);
lean_dec_ref(v_otherwise_x3f_1492_);
v___x_1554_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1553_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___y_1532_ = v_rhs_1545_;
v_otherwise_1533_ = v_a_1555_;
v___y_1534_ = v___y_1546_;
v___y_1535_ = v___y_1547_;
v___y_1536_ = v___y_1548_;
v___y_1537_ = v___y_1549_;
v___y_1538_ = v___y_1550_;
v___y_1539_ = v___y_1551_;
goto v___jp_1531_;
}
else
{
lean_dec_ref(v_rhs_1545_);
lean_dec(v_body_x3f_1493_);
lean_dec_ref(v_reassigned_1490_);
return v___x_1554_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1656_, lean_object* v_decl_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v_reassigns_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1657_);
v___x_1694_ = l_Lean_Syntax_isOfKind(v_decl_1657_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1657_);
v___x_1696_ = l_Lean_Syntax_isOfKind(v_decl_1657_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1697_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1698_ = lean_box(0);
v___x_1699_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1698_, v___x_1696_);
v___x_1700_ = l_Std_Format_defWidth;
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = l_Std_Format_pretty(v___x_1699_, v___x_1700_, v___x_1701_, v___x_1701_);
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1697_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
lean_inc_ref(v_a_1658_);
v___x_1705_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1704_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v_pattern_1707_; lean_object* v___y_1709_; lean_object* v_otherwise_x3f_1710_; lean_object* v_body_x3f_x3f_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v_body_x3f_x3f_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___x_1741_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v_pattern_1707_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1706_);
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1780_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1741_);
v___x_1781_ = l_Lean_Syntax_isNone(v___x_1780_);
if (v___x_1781_ == 0)
{
uint8_t v___x_1782_; 
lean_inc(v___x_1780_);
v___x_1782_ = l_Lean_Syntax_matchesNull(v___x_1780_, v___x_1741_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v___x_1780_);
lean_dec(v_pattern_1707_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1784_ = lean_box(0);
v___x_1785_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1784_, v___x_1782_);
v___x_1786_ = l_Std_Format_defWidth;
v___x_1787_ = l_Std_Format_pretty(v___x_1785_, v___x_1786_, v___x_1706_, v___x_1706_);
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1783_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
lean_inc_ref(v_a_1658_);
v___x_1790_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1789_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = l_Lean_Syntax_getArg(v___x_1780_, v___x_1706_);
lean_dec(v___x_1780_);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1793_ = l_Lean_Syntax_isOfKind(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_pattern_1707_);
v___x_1794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1795_ = lean_box(0);
v___x_1796_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1795_, v___x_1793_);
v___x_1797_ = l_Std_Format_defWidth;
v___x_1798_ = l_Std_Format_pretty(v___x_1796_, v___x_1797_, v___x_1706_, v___x_1706_);
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1794_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
lean_inc_ref(v_a_1658_);
v___x_1801_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1800_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1801_;
}
else
{
v___y_1743_ = v_a_1658_;
v___y_1744_ = v_a_1659_;
v___y_1745_ = v_a_1660_;
v___y_1746_ = v_a_1661_;
v___y_1747_ = v_a_1662_;
v___y_1748_ = v_a_1663_;
goto v___jp_1742_;
}
}
}
else
{
lean_dec(v___x_1780_);
v___y_1743_ = v_a_1658_;
v___y_1744_ = v_a_1659_;
v___y_1745_ = v_a_1660_;
v___y_1746_ = v_a_1661_;
v___y_1747_ = v_a_1662_;
v___y_1748_ = v_a_1663_;
goto v___jp_1742_;
}
v___jp_1708_:
{
if (v_reassignment_1656_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_pattern_1707_);
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1678_ = v_body_x3f_x3f_1711_;
v___y_1679_ = v_otherwise_x3f_1710_;
v___y_1680_ = v___y_1709_;
v_reassigns_1681_ = v___x_1718_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1714_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1717_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1707_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v___x_1719_);
v___y_1678_ = v_body_x3f_x3f_1711_;
v___y_1679_ = v_otherwise_x3f_1710_;
v___y_1680_ = v___y_1709_;
v_reassigns_1681_ = v_a_1720_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1714_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1717_;
goto v___jp_1677_;
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_body_x3f_x3f_1711_);
lean_dec(v_otherwise_x3f_1710_);
lean_dec(v___y_1709_);
v_a_1721_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1719_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
v___jp_1729_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1730_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_body_x3f_x3f_1732_);
v___y_1709_ = v___y_1731_;
v_otherwise_x3f_1710_ = v___x_1739_;
v_body_x3f_x3f_1711_ = v___x_1740_;
v___y_1712_ = v___y_1733_;
v___y_1713_ = v___y_1734_;
v___y_1714_ = v___y_1735_;
v___y_1715_ = v___y_1736_;
v___y_1716_ = v___y_1737_;
v___y_1717_ = v___y_1738_;
goto v___jp_1708_;
}
v___jp_1742_:
{
lean_object* v___x_1749_; lean_object* v_rhs_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1749_ = lean_unsigned_to_nat(3u);
v_rhs_1750_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1749_);
v___x_1751_ = lean_unsigned_to_nat(4u);
v___x_1752_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1751_);
v___x_1753_ = l_Lean_Syntax_isNone(v___x_1752_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; 
lean_inc(v___x_1752_);
v___x_1754_ = l_Lean_Syntax_matchesNull(v___x_1752_, v___x_1749_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v___x_1752_);
lean_dec(v_rhs_1750_);
lean_dec(v_pattern_1707_);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1756_ = lean_box(0);
v___x_1757_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1756_, v___x_1754_);
v___x_1758_ = l_Std_Format_defWidth;
v___x_1759_ = l_Std_Format_pretty(v___x_1757_, v___x_1758_, v___x_1706_, v___x_1706_);
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1755_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
lean_inc_ref(v___y_1743_);
v___x_1762_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1761_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; lean_object* v_otherwise_x3f_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1764_ = l_Lean_Syntax_getArg(v___x_1752_, v___x_1741_);
v___x_1765_ = l_Lean_Syntax_getArg(v___x_1752_, v___x_1763_);
lean_dec(v___x_1752_);
v___x_1766_ = l_Lean_Syntax_isNone(v___x_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; 
lean_inc(v___x_1765_);
v___x_1767_ = l_Lean_Syntax_matchesNull(v___x_1765_, v___x_1741_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v___x_1765_);
lean_dec(v_otherwise_x3f_1764_);
lean_dec(v_rhs_1750_);
lean_dec(v_pattern_1707_);
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1769_, v___x_1767_);
v___x_1771_ = l_Std_Format_defWidth;
v___x_1772_ = l_Std_Format_pretty(v___x_1770_, v___x_1771_, v___x_1706_, v___x_1706_);
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1768_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
lean_inc_ref(v___y_1743_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1774_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1775_;
}
else
{
lean_object* v_body_x3f_x3f_1776_; lean_object* v___x_1777_; 
lean_dec(v_decl_1657_);
v_body_x3f_x3f_1776_ = l_Lean_Syntax_getArg(v___x_1765_, v___x_1706_);
lean_dec(v___x_1765_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_body_x3f_x3f_1776_);
v___y_1730_ = v_otherwise_x3f_1764_;
v___y_1731_ = v_rhs_1750_;
v_body_x3f_x3f_1732_ = v___x_1777_;
v___y_1733_ = v___y_1743_;
v___y_1734_ = v___y_1744_;
v___y_1735_ = v___y_1745_;
v___y_1736_ = v___y_1746_;
v___y_1737_ = v___y_1747_;
v___y_1738_ = v___y_1748_;
goto v___jp_1729_;
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v___x_1765_);
lean_dec(v_decl_1657_);
v___x_1778_ = lean_box(0);
v___y_1730_ = v_otherwise_x3f_1764_;
v___y_1731_ = v_rhs_1750_;
v_body_x3f_x3f_1732_ = v___x_1778_;
v___y_1733_ = v___y_1743_;
v___y_1734_ = v___y_1744_;
v___y_1735_ = v___y_1745_;
v___y_1736_ = v___y_1746_;
v___y_1737_ = v___y_1747_;
v___y_1738_ = v___y_1748_;
goto v___jp_1729_;
}
}
}
else
{
lean_object* v___x_1779_; 
lean_dec(v___x_1752_);
lean_dec(v_decl_1657_);
v___x_1779_ = lean_box(0);
v___y_1709_ = v_rhs_1750_;
v_otherwise_x3f_1710_ = v___x_1779_;
v_body_x3f_x3f_1711_ = v___x_1779_;
v___y_1712_ = v___y_1743_;
v___y_1713_ = v___y_1744_;
v___y_1714_ = v___y_1745_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1747_;
v___y_1717_ = v___y_1748_;
goto v___jp_1708_;
}
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v_x_1803_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v_x_1803_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1802_);
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1803_);
v___x_1818_ = l_Lean_Syntax_isOfKind(v_x_1803_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec(v_x_1803_);
v___x_1819_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1820_ = lean_box(0);
v___x_1821_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1820_, v___x_1818_);
v___x_1822_ = l_Std_Format_defWidth;
v___x_1823_ = l_Std_Format_pretty(v___x_1821_, v___x_1822_, v___x_1802_, v___x_1802_);
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1819_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
lean_inc_ref(v_a_1658_);
v___x_1826_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1825_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1827_);
v___x_1829_ = l_Lean_Syntax_isNone(v___x_1828_);
if (v___x_1829_ == 0)
{
uint8_t v___x_1830_; 
lean_inc(v___x_1828_);
v___x_1830_ = l_Lean_Syntax_matchesNull(v___x_1828_, v___x_1827_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v___x_1828_);
lean_dec(v_x_1803_);
v___x_1831_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1832_, v___x_1830_);
v___x_1834_ = l_Std_Format_defWidth;
v___x_1835_ = l_Std_Format_pretty(v___x_1833_, v___x_1834_, v___x_1802_, v___x_1802_);
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1831_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
lean_inc_ref(v_a_1658_);
v___x_1838_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1837_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1828_, v___x_1802_);
lean_dec(v___x_1828_);
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1841_ = l_Lean_Syntax_isOfKind(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v_x_1803_);
v___x_1842_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1843_ = lean_box(0);
v___x_1844_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1843_, v___x_1841_);
v___x_1845_ = l_Std_Format_defWidth;
v___x_1846_ = l_Std_Format_pretty(v___x_1844_, v___x_1845_, v___x_1802_, v___x_1802_);
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1842_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
lean_inc_ref(v_a_1658_);
v___x_1849_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1848_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1849_;
}
else
{
v___y_1805_ = v_a_1658_;
v___y_1806_ = v_a_1659_;
v___y_1807_ = v_a_1660_;
v___y_1808_ = v_a_1661_;
v___y_1809_ = v_a_1662_;
v___y_1810_ = v_a_1663_;
goto v___jp_1804_;
}
}
}
else
{
lean_dec(v___x_1828_);
v___y_1805_ = v_a_1658_;
v___y_1806_ = v_a_1659_;
v___y_1807_ = v_a_1660_;
v___y_1808_ = v_a_1661_;
v___y_1809_ = v_a_1662_;
v___y_1810_ = v_a_1663_;
goto v___jp_1804_;
}
}
v___jp_1804_:
{
lean_object* v___x_1811_; lean_object* v_rhs_1812_; 
v___x_1811_ = lean_unsigned_to_nat(3u);
v_rhs_1812_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1811_);
lean_dec(v_decl_1657_);
if (v_reassignment_1656_ == 0)
{
lean_object* v___x_1813_; 
lean_dec(v_x_1803_);
v___x_1813_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1666_ = v___y_1805_;
v___y_1667_ = v_rhs_1812_;
v___y_1668_ = v___y_1810_;
v___y_1669_ = v___y_1809_;
v___y_1670_ = v___y_1808_;
v___y_1671_ = v___y_1807_;
v___y_1672_ = v___y_1806_;
v___y_1673_ = v___x_1813_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_mk_empty_array_with_capacity(v___x_1814_);
v___x_1816_ = lean_array_push(v___x_1815_, v_x_1803_);
v___y_1666_ = v___y_1805_;
v___y_1667_ = v_rhs_1812_;
v___y_1668_ = v___y_1810_;
v___y_1669_ = v___y_1809_;
v___y_1670_ = v___y_1808_;
v___y_1671_ = v___y_1807_;
v___y_1672_ = v___y_1806_;
v___y_1673_ = v___x_1816_;
goto v___jp_1665_;
}
}
}
v___jp_1665_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1667_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1673_, v___x_1674_, v___x_1675_, v___x_1675_, v___y_1666_, v___y_1672_, v___y_1671_, v___y_1670_, v___y_1669_, v___y_1668_);
return v___x_1676_;
}
v___jp_1677_:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___y_1680_);
if (lean_obj_tag(v___y_1678_) == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1681_, v___x_1688_, v___y_1679_, v___x_1689_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1692_; 
v_val_1691_ = lean_ctor_get(v___y_1678_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v___y_1678_);
v___x_1692_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1681_, v___x_1688_, v___y_1679_, v_val_1691_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1952_, size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_b_1955_);
return v___x_1964_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1965_ = lean_array_uget_borrowed(v_as_1952_, v_i_1954_);
lean_inc(v_a_1965_);
v___x_1966_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1965_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; size_t v___x_1969_; size_t v___x_1970_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1966_);
v___x_1968_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1967_, v_b_1955_);
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1954_, v___x_1969_);
v_i_1954_ = v___x_1970_;
v_b_1955_ = v___x_1968_;
goto _start;
}
else
{
lean_dec_ref(v_b_1955_);
return v___x_1966_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_1986_ = l_Lean_stringToMessageData(v___x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2001_, lean_object* v_as_2002_, size_t v_sz_2003_, size_t v_i_2004_, lean_object* v_b_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_a_2014_; uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2004_, v_sz_2003_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_b_2005_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v_a_2021_; uint8_t v___x_2022_; 
v___x_2020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2021_ = lean_array_uget_borrowed(v_as_2002_, v_i_2004_);
lean_inc(v_a_2021_);
v___x_2022_ = l_Lean_Syntax_isOfKind(v_a_2021_, v___x_2020_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_dec_ref(v___x_2023_);
v_a_2014_ = v_b_2005_;
goto v___jp_2013_;
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_b_2005_);
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___y_2035_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_unsigned_to_nat(3u);
v___x_2052_ = l_Lean_Syntax_getArg(v_a_2021_, v___x_2032_);
v___x_2053_ = l_Lean_Syntax_getArgs(v___x_2052_);
lean_dec(v___x_2052_);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2056_ = lean_array_get_size(v___x_2053_);
v___x_2057_ = lean_nat_dec_lt(v___x_2054_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_dec_ref(v___x_2053_);
v___y_2035_ = v___x_2055_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2058_ = lean_box(v___x_2022_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___x_2055_);
v___x_2060_ = lean_nat_dec_le(v___x_2056_, v___x_2056_);
if (v___x_2060_ == 0)
{
if (v___x_2057_ == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2053_);
v___y_2035_ = v___x_2055_;
goto v___jp_2034_;
}
else
{
size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; lean_object* v_snd_2064_; 
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = lean_usize_of_nat(v___x_2056_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2022_, v___x_2001_, v___x_2053_, v___x_2061_, v___x_2062_, v___x_2059_);
lean_dec_ref(v___x_2053_);
v_snd_2064_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_snd_2064_);
lean_dec_ref(v___x_2063_);
v___y_2035_ = v_snd_2064_;
goto v___jp_2034_;
}
}
else
{
size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; lean_object* v_snd_2068_; 
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2056_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2022_, v___x_2001_, v___x_2053_, v___x_2065_, v___x_2066_, v___x_2059_);
lean_dec_ref(v___x_2053_);
v_snd_2068_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_snd_2068_);
lean_dec_ref(v___x_2067_);
v___y_2035_ = v_snd_2068_;
goto v___jp_2034_;
}
}
v___jp_2034_:
{
size_t v_sz_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v_sz_2036_ = lean_array_size(v___y_2035_);
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2036_, v___x_2037_, v___y_2035_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_dec_ref(v___x_2039_);
v_a_2014_ = v_b_2005_;
goto v___jp_2013_;
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_b_2005_);
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
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
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref(v___x_2038_);
v___x_2048_ = l_Lean_Syntax_getArg(v_a_2021_, v___x_2033_);
v___x_2049_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2048_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2005_, v_a_2050_);
v_a_2014_ = v___x_2051_;
goto v___jp_2013_;
}
else
{
lean_dec_ref(v_b_2005_);
return v___x_2049_;
}
}
}
}
}
v___jp_2013_:
{
size_t v___x_2015_; size_t v___x_2016_; 
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_add(v_i_2004_, v___x_2015_);
v_i_2004_ = v___x_2016_;
v_b_2005_ = v_a_2014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2069_, size_t v_sz_2070_, size_t v_i_2071_, lean_object* v_b_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_a_2081_; uint8_t v___x_2085_; 
v___x_2085_ = lean_usize_dec_lt(v_i_2071_, v_sz_2070_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_b_2072_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v_a_2088_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v_a_2088_ = lean_array_uget_borrowed(v_as_2069_, v_i_2071_);
v___x_2101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2088_);
v___x_2102_ = l_Lean_Syntax_isOfKind(v_a_2088_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2088_);
v___x_2104_ = l_Lean_Syntax_isOfKind(v_a_2088_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2106_ = lean_box(0);
lean_inc(v_a_2088_);
v___x_2107_ = l_Lean_Syntax_formatStx(v_a_2088_, v___x_2106_, v___x_2104_);
v___x_2108_ = l_Std_Format_defWidth;
v___x_2109_ = l_Std_Format_pretty(v___x_2107_, v___x_2108_, v___x_2087_, v___x_2087_);
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2105_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_inc_ref(v___y_2073_);
v___x_2112_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2111_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_dec_ref(v___x_2112_);
v_a_2081_ = v_b_2072_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_b_2072_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2121_ = lean_unsigned_to_nat(1u);
v___x_2122_ = l_Lean_Syntax_getArg(v_a_2088_, v___x_2121_);
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2122_);
v___x_2124_ = l_Lean_Syntax_isOfKind(v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v___x_2122_);
v___x_2125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2126_ = lean_box(0);
lean_inc(v_a_2088_);
v___x_2127_ = l_Lean_Syntax_formatStx(v_a_2088_, v___x_2126_, v___x_2124_);
v___x_2128_ = l_Std_Format_defWidth;
v___x_2129_ = l_Std_Format_pretty(v___x_2127_, v___x_2128_, v___x_2087_, v___x_2087_);
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2125_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
lean_inc_ref(v___y_2073_);
v___x_2132_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2131_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_dec_ref(v___x_2132_);
v_a_2081_ = v_b_2072_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_b_2072_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; size_t v_sz_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2141_ = l_Lean_Syntax_getArg(v___x_2122_, v___x_2087_);
lean_dec(v___x_2122_);
v___x_2142_ = l_Lean_Syntax_getArgs(v___x_2141_);
lean_dec(v___x_2141_);
v_sz_2143_ = lean_array_size(v___x_2142_);
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2102_, v___x_2142_, v_sz_2143_, v___x_2144_, v_b_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec_ref(v___x_2142_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2145_);
v_a_2081_ = v_a_2146_;
goto v___jp_2080_;
}
else
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2147_ = lean_unsigned_to_nat(2u);
v___x_2148_ = l_Lean_Syntax_getArg(v_a_2088_, v___x_2147_);
v___x_2149_ = l_Lean_Syntax_isNone(v___x_2148_);
if (v___x_2149_ == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = l_Lean_Syntax_matchesNull(v___x_2148_, v___x_2147_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2151_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2152_ = lean_box(0);
lean_inc(v_a_2088_);
v___x_2153_ = l_Lean_Syntax_formatStx(v_a_2088_, v___x_2152_, v___x_2150_);
v___x_2154_ = l_Std_Format_defWidth;
v___x_2155_ = l_Std_Format_pretty(v___x_2153_, v___x_2154_, v___x_2087_, v___x_2087_);
v___x_2156_ = l_Lean_stringToMessageData(v___x_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2151_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
lean_inc_ref(v___y_2073_);
v___x_2158_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2157_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_dec_ref(v___x_2158_);
v_a_2081_ = v_b_2072_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v_b_2072_);
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
v___y_2090_ = v___y_2073_;
v___y_2091_ = v___y_2074_;
v___y_2092_ = v___y_2075_;
v___y_2093_ = v___y_2076_;
v___y_2094_ = v___y_2077_;
v___y_2095_ = v___y_2078_;
goto v___jp_2089_;
}
}
else
{
lean_dec(v___x_2148_);
v___y_2090_ = v___y_2073_;
v___y_2091_ = v___y_2074_;
v___y_2092_ = v___y_2075_;
v___y_2093_ = v___y_2076_;
v___y_2094_ = v___y_2077_;
v___y_2095_ = v___y_2078_;
goto v___jp_2089_;
}
}
v___jp_2089_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_unsigned_to_nat(4u);
v___x_2097_ = l_Lean_Syntax_getArg(v_a_2088_, v___x_2096_);
v___x_2098_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2097_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
v___x_2100_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2099_, v_b_2072_);
v_a_2081_ = v___x_2100_;
goto v___jp_2080_;
}
else
{
lean_dec_ref(v_b_2072_);
return v___x_2098_;
}
}
}
v___jp_2080_:
{
size_t v___x_2082_; size_t v___x_2083_; 
v___x_2082_ = ((size_t)1ULL);
v___x_2083_ = lean_usize_add(v_i_2071_, v___x_2082_);
v_i_2071_ = v___x_2083_;
v_b_2072_ = v_a_2081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2167_) == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
else
{
lean_object* v_val_2177_; lean_object* v___x_2178_; 
v_val_2177_ = lean_ctor_get(v_stx_x3f_2167_, 0);
lean_inc(v_val_2177_);
lean_dec_ref(v_stx_x3f_2167_);
v___x_2178_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2177_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2185_, lean_object* v_as_2186_, size_t v_sz_2187_, size_t v_i_2188_, lean_object* v_b_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_a_2198_; uint8_t v___x_2202_; 
v___x_2202_ = lean_usize_dec_lt(v_i_2188_, v_sz_2187_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_b_2189_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v_a_2205_; uint8_t v___x_2206_; 
v___x_2204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2205_ = lean_array_uget_borrowed(v_as_2186_, v_i_2188_);
lean_inc(v_a_2205_);
v___x_2206_ = l_Lean_Syntax_isOfKind(v_a_2205_, v___x_2204_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_dec_ref(v___x_2207_);
v_a_2198_ = v_b_2189_;
goto v___jp_2197_;
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v_b_2189_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___y_2219_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_unsigned_to_nat(3u);
v___x_2236_ = l_Lean_Syntax_getArg(v_a_2205_, v___x_2216_);
v___x_2237_ = l_Lean_Syntax_getArgs(v___x_2236_);
lean_dec(v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2240_ = lean_array_get_size(v___x_2237_);
v___x_2241_ = lean_nat_dec_lt(v___x_2238_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_dec_ref(v___x_2237_);
v___y_2219_ = v___x_2239_;
goto v___jp_2218_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2242_ = lean_box(v___x_2206_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___x_2239_);
v___x_2244_ = lean_nat_dec_le(v___x_2240_, v___x_2240_);
if (v___x_2244_ == 0)
{
if (v___x_2241_ == 0)
{
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2237_);
v___y_2219_ = v___x_2239_;
goto v___jp_2218_;
}
else
{
size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; lean_object* v_snd_2248_; 
v___x_2245_ = ((size_t)0ULL);
v___x_2246_ = lean_usize_of_nat(v___x_2240_);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2206_, v___x_2185_, v___x_2237_, v___x_2245_, v___x_2246_, v___x_2243_);
lean_dec_ref(v___x_2237_);
v_snd_2248_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_snd_2248_);
lean_dec_ref(v___x_2247_);
v___y_2219_ = v_snd_2248_;
goto v___jp_2218_;
}
}
else
{
size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; lean_object* v_snd_2252_; 
v___x_2249_ = ((size_t)0ULL);
v___x_2250_ = lean_usize_of_nat(v___x_2240_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2206_, v___x_2185_, v___x_2237_, v___x_2249_, v___x_2250_, v___x_2243_);
lean_dec_ref(v___x_2237_);
v_snd_2252_ = lean_ctor_get(v___x_2251_, 1);
lean_inc(v_snd_2252_);
lean_dec_ref(v___x_2251_);
v___y_2219_ = v_snd_2252_;
goto v___jp_2218_;
}
}
v___jp_2218_:
{
size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v_sz_2220_ = lean_array_size(v___y_2219_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2220_, v___x_2221_, v___y_2219_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_dec_ref(v___x_2223_);
v_a_2198_ = v_b_2189_;
goto v___jp_2197_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref(v_b_2189_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v___x_2222_);
v___x_2232_ = l_Lean_Syntax_getArg(v_a_2205_, v___x_2217_);
v___x_2233_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2232_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref(v___x_2233_);
v___x_2235_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2189_, v_a_2234_);
v_a_2198_ = v___x_2235_;
goto v___jp_2197_;
}
else
{
lean_dec_ref(v_b_2189_);
return v___x_2233_;
}
}
}
}
}
v___jp_2197_:
{
size_t v___x_2199_; size_t v___x_2200_; 
v___x_2199_ = ((size_t)1ULL);
v___x_2200_ = lean_usize_add(v_i_2188_, v___x_2199_);
v_i_2188_ = v___x_2200_;
v_b_2189_ = v_a_2198_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2289_ = l_Lean_NameSet_empty;
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = 0;
v___x_2292_ = 1;
v___x_2293_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2293_, 0, v___x_2290_);
lean_ctor_set(v___x_2293_, 1, v___x_2289_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*2, v___x_2292_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*2 + 1, v___x_2291_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*2 + 2, v___x_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2337_; lean_object* v_bodyInfo_2338_; lean_object* v___y_2342_; lean_object* v_bodyInfo_2343_; lean_object* v___x_2346_; lean_object* v_env_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = lean_st_ref_get(v_a_2300_);
v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc_ref(v_env_2347_);
lean_dec(v___x_2346_);
lean_inc(v_stx_2294_);
v___x_2348_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2348_, 0, v_env_2347_);
lean_closure_set(v___x_2348_, 1, v_stx_2294_);
lean_inc_ref(v_a_2299_);
v___x_2349_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2348_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_4154_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_4154_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_4154_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
if (lean_obj_tag(v_a_2350_) == 1)
{
lean_object* v_val_2354_; lean_object* v_snd_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_del_object(v___x_2352_);
lean_dec(v_stx_2294_);
v_val_2354_ = lean_ctor_get(v_a_2350_, 0);
lean_inc(v_val_2354_);
lean_dec_ref(v_a_2350_);
v_snd_2355_ = lean_ctor_get(v_val_2354_, 1);
lean_inc(v_snd_2355_);
lean_dec(v_val_2354_);
v___x_2356_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2356_, 0, lean_box(0));
lean_closure_set(v___x_2356_, 1, v_snd_2355_);
lean_inc_ref(v_a_2299_);
v___x_2357_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2356_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v_stx_2294_ = v_a_2358_;
goto _start;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2357_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2357_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___x_2429_; uint8_t v___x_2430_; uint8_t v___x_2431_; 
lean_dec(v_a_2350_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
lean_inc(v_stx_2294_);
v___x_2430_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2429_);
v___x_2431_ = 1;
if (v___x_2430_ == 0)
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2294_);
v___x_2433_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2294_);
v___x_2435_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2294_);
v___x_2437_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2294_);
v___x_2439_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2294_);
v___x_2441_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; uint8_t v___x_2443_; 
lean_del_object(v___x_2352_);
v___x_2442_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2294_);
v___x_2443_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2294_);
v___x_2445_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; 
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2294_);
v___x_2447_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2294_);
v___x_2459_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2294_);
v___x_2461_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2294_);
v___x_2463_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2294_);
v___x_2465_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2294_);
v___x_2467_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2294_);
v___x_2469_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2294_);
v___x_2471_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2294_);
v___x_2473_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2294_);
v___x_2475_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2294_);
v___x_2477_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2294_);
v___x_2479_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51));
lean_inc(v_stx_2294_);
v___x_2481_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53));
lean_inc(v_stx_2294_);
v___x_2483_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55));
lean_inc(v_stx_2294_);
v___x_2485_ = l_Lean_Syntax_isOfKind(v_stx_2294_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v_env_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2486_ = lean_st_ref_get(v_a_2300_);
v_env_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc_ref(v_env_2487_);
lean_dec(v___x_2486_);
v___x_2488_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2489_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2490_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2488_, v_env_2487_, v___x_2489_);
v___x_2491_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2492_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2490_, v___x_2491_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2523_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2523_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2523_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_fst_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2521_; 
v_fst_2497_ = lean_ctor_get(v_a_2493_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2493_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v_a_2493_, 1);
lean_dec(v_unused_2522_);
v___x_2499_ = v_a_2493_;
v_isShared_2500_ = v_isSharedCheck_2521_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_fst_2497_);
lean_dec(v_a_2493_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2521_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
if (lean_obj_tag(v_fst_2497_) == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_del_object(v___x_2495_);
v___x_2501_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2502_ = l_Lean_MessageData_ofName(v___x_2489_);
lean_inc_ref(v___x_2502_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set_tag(v___x_2499_, 7);
lean_ctor_set(v___x_2499_, 1, v___x_2502_);
lean_ctor_set(v___x_2499_, 0, v___x_2501_);
v___x_2504_ = v___x_2499_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2505_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2508_ = l_Lean_indentD(v___x_2507_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2506_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___x_2502_);
v___x_2513_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
lean_inc_ref(v_a_2295_);
v___x_2515_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2514_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2515_;
}
}
else
{
lean_object* v_val_2517_; lean_object* v___x_2519_; 
lean_del_object(v___x_2499_);
lean_dec(v___x_2489_);
lean_dec(v_stx_2294_);
v_val_2517_ = lean_ctor_get(v_fst_2497_, 0);
lean_inc(v_val_2517_);
lean_dec_ref(v_fst_2497_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_val_2517_);
v___x_2519_ = v___x_2495_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_val_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v___x_2489_);
lean_dec(v_stx_2294_);
v_a_2524_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2492_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2492_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___y_2536_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_unsigned_to_nat(5u);
v___x_2534_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2533_);
v___x_2545_ = lean_unsigned_to_nat(6u);
v___x_2546_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2545_);
lean_dec(v_stx_2294_);
v___x_2547_ = l_Lean_Syntax_getOptional_x3f(v___x_2546_);
lean_dec(v___x_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_box(0);
v___y_2536_ = v___x_2548_;
goto v___jp_2535_;
}
else
{
lean_object* v_val_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_val_2549_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2547_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_val_2549_);
lean_dec(v___x_2547_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_val_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
v___y_2536_ = v___x_2554_;
goto v___jp_2535_;
}
}
}
v___jp_2535_:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2534_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2537_) == 0)
{
if (lean_obj_tag(v___y_2536_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = l_Lean_NameSet_empty;
v___x_2540_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2540_, 0, v___x_2532_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*2, v___x_2483_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*2 + 1, v___x_2483_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*2 + 2, v___x_2483_);
v___y_2342_ = v_a_2538_;
v_bodyInfo_2343_ = v___x_2540_;
goto v___jp_2341_;
}
else
{
lean_object* v_a_2541_; lean_object* v_val_2542_; lean_object* v___x_2543_; 
v_a_2541_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2537_);
v_val_2542_ = lean_ctor_get(v___y_2536_, 0);
lean_inc(v_val_2542_);
lean_dec_ref(v___y_2536_);
v___x_2543_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2542_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v___y_2342_ = v_a_2541_;
v_bodyInfo_2343_ = v_a_2544_;
goto v___jp_2341_;
}
else
{
lean_dec(v_a_2541_);
return v___x_2543_;
}
}
}
else
{
lean_dec(v___y_2536_);
return v___x_2537_;
}
}
}
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___y_2561_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2557_ = lean_unsigned_to_nat(1u);
v___x_2558_ = lean_unsigned_to_nat(5u);
v___x_2559_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2558_);
v___x_2570_ = lean_unsigned_to_nat(6u);
v___x_2571_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2570_);
lean_dec(v_stx_2294_);
v___x_2572_ = l_Lean_Syntax_getOptional_x3f(v___x_2571_);
lean_dec(v___x_2571_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_box(0);
v___y_2561_ = v___x_2573_;
goto v___jp_2560_;
}
else
{
lean_object* v_val_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_val_2574_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2572_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_val_2574_);
lean_dec(v___x_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_val_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
v___y_2561_ = v___x_2579_;
goto v___jp_2560_;
}
}
}
v___jp_2560_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2559_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2562_) == 0)
{
if (lean_obj_tag(v___y_2561_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = l_Lean_NameSet_empty;
v___x_2565_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2565_, 0, v___x_2557_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*2, v___x_2481_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*2 + 1, v___x_2481_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*2 + 2, v___x_2481_);
v___y_2337_ = v_a_2563_;
v_bodyInfo_2338_ = v___x_2565_;
goto v___jp_2336_;
}
else
{
lean_object* v_a_2566_; lean_object* v_val_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2566_);
lean_dec_ref(v___x_2562_);
v_val_2567_ = lean_ctor_get(v___y_2561_, 0);
lean_inc(v_val_2567_);
lean_dec_ref(v___y_2561_);
v___x_2568_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2567_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref(v___x_2568_);
v___y_2337_ = v_a_2566_;
v_bodyInfo_2338_ = v_a_2569_;
goto v___jp_2336_;
}
else
{
lean_dec(v_a_2566_);
return v___x_2568_;
}
}
}
else
{
lean_dec(v___y_2561_);
return v___x_2562_;
}
}
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2797_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2583_);
v___x_2798_ = l_Lean_Syntax_isNone(v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = lean_unsigned_to_nat(5u);
v___x_2800_ = l_Lean_Syntax_matchesNull(v___x_2797_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v_env_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2801_ = lean_st_ref_get(v_a_2300_);
v_env_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_ref(v_env_2802_);
lean_dec(v___x_2801_);
v___x_2803_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2804_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2805_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2803_, v_env_2802_, v___x_2804_);
v___x_2806_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2807_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2805_, v___x_2806_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2838_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2838_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2838_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v_fst_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2836_; 
v_fst_2812_ = lean_ctor_get(v_a_2808_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_a_2808_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v_a_2808_, 1);
lean_dec(v_unused_2837_);
v___x_2814_ = v_a_2808_;
v_isShared_2815_ = v_isSharedCheck_2836_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_fst_2812_);
lean_dec(v_a_2808_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2836_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_fst_2812_) == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
lean_del_object(v___x_2810_);
v___x_2816_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2817_ = l_Lean_MessageData_ofName(v___x_2804_);
lean_inc_ref(v___x_2817_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 7);
lean_ctor_set(v___x_2814_, 1, v___x_2817_);
lean_ctor_set(v___x_2814_, 0, v___x_2816_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2820_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2823_ = l_Lean_indentD(v___x_2822_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
lean_ctor_set(v___x_2827_, 1, v___x_2817_);
v___x_2828_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
lean_inc_ref(v_a_2295_);
v___x_2830_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2829_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2830_;
}
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2834_; 
lean_del_object(v___x_2814_);
lean_dec(v___x_2804_);
lean_dec(v_stx_2294_);
v_val_2832_ = lean_ctor_get(v_fst_2812_, 0);
lean_inc(v_val_2832_);
lean_dec_ref(v_fst_2812_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v_val_2832_);
v___x_2834_ = v___x_2810_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_val_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v___x_2804_);
lean_dec(v_stx_2294_);
v_a_2839_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2807_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2807_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
v___y_2585_ = v_a_2295_;
v___y_2586_ = v_a_2296_;
v___y_2587_ = v_a_2297_;
v___y_2588_ = v_a_2298_;
v___y_2589_ = v_a_2299_;
v___y_2590_ = v_a_2300_;
goto v___jp_2584_;
}
}
else
{
lean_dec(v___x_2797_);
v___y_2585_ = v_a_2295_;
v___y_2586_ = v_a_2296_;
v___y_2587_ = v_a_2297_;
v___y_2588_ = v_a_2298_;
v___y_2589_ = v_a_2299_;
v___y_2590_ = v_a_2300_;
goto v___jp_2584_;
}
v___jp_2584_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2591_ = lean_unsigned_to_nat(4u);
v___x_2592_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57));
lean_inc(v___x_2592_);
v___x_2594_ = l_Lean_Syntax_isOfKind(v___x_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; lean_object* v_env_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec(v___x_2592_);
v___x_2595_ = lean_st_ref_get(v___y_2590_);
v_env_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_ref(v_env_2596_);
lean_dec(v___x_2595_);
v___x_2597_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2598_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2599_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2597_, v_env_2596_, v___x_2598_);
v___x_2600_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2601_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2599_, v___x_2600_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2632_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2632_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2632_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_fst_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2630_; 
v_fst_2606_ = lean_ctor_get(v_a_2602_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_a_2602_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v_a_2602_, 1);
lean_dec(v_unused_2631_);
v___x_2608_ = v_a_2602_;
v_isShared_2609_ = v_isSharedCheck_2630_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_fst_2606_);
lean_dec(v_a_2602_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2630_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
if (lean_obj_tag(v_fst_2606_) == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_del_object(v___x_2604_);
v___x_2610_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2611_ = l_Lean_MessageData_ofName(v___x_2598_);
lean_inc_ref(v___x_2611_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set_tag(v___x_2608_, 7);
lean_ctor_set(v___x_2608_, 1, v___x_2611_);
lean_ctor_set(v___x_2608_, 0, v___x_2610_);
v___x_2613_ = v___x_2608_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2614_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2617_ = l_Lean_indentD(v___x_2616_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2615_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___x_2611_);
v___x_2622_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
lean_inc_ref(v___y_2585_);
v___x_2624_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2623_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2624_;
}
}
else
{
lean_object* v_val_2626_; lean_object* v___x_2628_; 
lean_del_object(v___x_2608_);
lean_dec(v___x_2598_);
lean_dec(v_stx_2294_);
v_val_2626_ = lean_ctor_get(v_fst_2606_, 0);
lean_inc(v_val_2626_);
lean_dec_ref(v_fst_2606_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v_val_2626_);
v___x_2628_ = v___x_2604_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_val_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v___x_2598_);
lean_dec(v_stx_2294_);
v_a_2633_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2601_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2601_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; size_t v_sz_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___x_2641_ = l_Lean_Syntax_getArg(v___x_2592_, v___x_2582_);
v___x_2642_ = l_Lean_Syntax_getArgs(v___x_2641_);
lean_dec(v___x_2641_);
v_sz_2643_ = lean_array_size(v___x_2642_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2643_, v___x_2644_, v___x_2642_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2646_; lean_object* v_env_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v___x_2592_);
v___x_2646_ = lean_st_ref_get(v___y_2590_);
v_env_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc_ref(v_env_2647_);
lean_dec(v___x_2646_);
v___x_2648_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2649_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2650_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2648_, v_env_2647_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2652_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2650_, v___x_2651_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2683_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2683_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2683_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_fst_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2681_; 
v_fst_2657_ = lean_ctor_get(v_a_2653_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v_a_2653_, 1);
lean_dec(v_unused_2682_);
v___x_2659_ = v_a_2653_;
v_isShared_2660_ = v_isSharedCheck_2681_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_fst_2657_);
lean_dec(v_a_2653_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2681_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
if (lean_obj_tag(v_fst_2657_) == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
lean_del_object(v___x_2655_);
v___x_2661_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2662_ = l_Lean_MessageData_ofName(v___x_2649_);
lean_inc_ref(v___x_2662_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set_tag(v___x_2659_, 7);
lean_ctor_set(v___x_2659_, 1, v___x_2662_);
lean_ctor_set(v___x_2659_, 0, v___x_2661_);
v___x_2664_ = v___x_2659_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2665_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2668_ = l_Lean_indentD(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2666_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___x_2662_);
v___x_2673_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
lean_inc_ref(v___y_2585_);
v___x_2675_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2674_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2675_;
}
}
else
{
lean_object* v_val_2677_; lean_object* v___x_2679_; 
lean_del_object(v___x_2659_);
lean_dec(v___x_2649_);
lean_dec(v_stx_2294_);
v_val_2677_ = lean_ctor_get(v_fst_2657_, 0);
lean_inc(v_val_2677_);
lean_dec_ref(v_fst_2657_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v_val_2677_);
v___x_2679_ = v___x_2655_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_val_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v___x_2649_);
lean_dec(v_stx_2294_);
v_a_2684_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2652_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2652_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_val_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_val_2692_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_val_2692_);
lean_dec_ref(v___x_2645_);
v___x_2693_ = l_Lean_Syntax_getArg(v___x_2592_, v___x_2583_);
lean_dec(v___x_2592_);
v___x_2694_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59));
lean_inc(v___x_2693_);
v___x_2695_ = l_Lean_Syntax_isOfKind(v___x_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v_env_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_dec(v___x_2693_);
lean_dec(v_val_2692_);
v___x_2696_ = lean_st_ref_get(v___y_2590_);
v_env_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc_ref(v_env_2697_);
lean_dec(v___x_2696_);
v___x_2698_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2699_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2700_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2698_, v_env_2697_, v___x_2699_);
v___x_2701_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2702_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2700_, v___x_2701_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2733_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2733_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2733_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_fst_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2731_; 
v_fst_2707_ = lean_ctor_get(v_a_2703_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_a_2703_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v_a_2703_, 1);
lean_dec(v_unused_2732_);
v___x_2709_ = v_a_2703_;
v_isShared_2710_ = v_isSharedCheck_2731_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_fst_2707_);
lean_dec(v_a_2703_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2731_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
if (lean_obj_tag(v_fst_2707_) == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_del_object(v___x_2705_);
v___x_2711_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2712_ = l_Lean_MessageData_ofName(v___x_2699_);
lean_inc_ref(v___x_2712_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 7);
lean_ctor_set(v___x_2709_, 1, v___x_2712_);
lean_ctor_set(v___x_2709_, 0, v___x_2711_);
v___x_2714_ = v___x_2709_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2715_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2718_ = l_Lean_indentD(v___x_2717_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2716_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___x_2712_);
v___x_2723_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
lean_inc_ref(v___y_2585_);
v___x_2725_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2724_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2725_;
}
}
else
{
lean_object* v_val_2727_; lean_object* v___x_2729_; 
lean_del_object(v___x_2709_);
lean_dec(v___x_2699_);
lean_dec(v_stx_2294_);
v_val_2727_ = lean_ctor_get(v_fst_2707_, 0);
lean_inc(v_val_2727_);
lean_dec_ref(v_fst_2707_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v_val_2727_);
v___x_2729_ = v___x_2705_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_val_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v___x_2699_);
lean_dec(v_stx_2294_);
v_a_2734_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2702_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2702_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2742_ = l_Lean_Syntax_getArg(v___x_2693_, v___x_2583_);
v___x_2743_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61));
v___x_2744_ = l_Lean_Syntax_isOfKind(v___x_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v_env_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec(v___x_2693_);
lean_dec(v_val_2692_);
v___x_2745_ = lean_st_ref_get(v___y_2590_);
v_env_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_ref(v_env_2746_);
lean_dec(v___x_2745_);
v___x_2747_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2748_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2749_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2747_, v_env_2746_, v___x_2748_);
v___x_2750_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2751_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2749_, v___x_2750_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2782_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2782_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2782_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_fst_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2780_; 
v_fst_2756_ = lean_ctor_get(v_a_2752_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; 
v_unused_2781_ = lean_ctor_get(v_a_2752_, 1);
lean_dec(v_unused_2781_);
v___x_2758_ = v_a_2752_;
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_fst_2756_);
lean_dec(v_a_2752_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
if (lean_obj_tag(v_fst_2756_) == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
lean_del_object(v___x_2754_);
v___x_2760_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2761_ = l_Lean_MessageData_ofName(v___x_2748_);
lean_inc_ref(v___x_2761_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 7);
lean_ctor_set(v___x_2758_, 1, v___x_2761_);
lean_ctor_set(v___x_2758_, 0, v___x_2760_);
v___x_2763_ = v___x_2758_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2764_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2767_ = l_Lean_indentD(v___x_2766_);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2765_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v___x_2761_);
v___x_2772_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
lean_inc_ref(v___y_2585_);
v___x_2774_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2773_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2774_;
}
}
else
{
lean_object* v_val_2776_; lean_object* v___x_2778_; 
lean_del_object(v___x_2758_);
lean_dec(v___x_2748_);
lean_dec(v_stx_2294_);
v_val_2776_ = lean_ctor_get(v_fst_2756_, 0);
lean_inc(v_val_2776_);
lean_dec_ref(v_fst_2756_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_val_2776_);
v___x_2778_ = v___x_2754_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_val_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v___x_2748_);
lean_dec(v_stx_2294_);
v_a_2783_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2751_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2751_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
lean_dec(v_stx_2294_);
v___x_2791_ = lean_unsigned_to_nat(3u);
v___x_2792_ = l_Lean_Syntax_getArg(v___x_2693_, v___x_2791_);
lean_dec(v___x_2693_);
v___x_2793_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2792_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; size_t v_sz_2795_; lean_object* v___x_2796_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref(v___x_2793_);
v_sz_2795_ = lean_array_size(v_val_2692_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2692_, v_sz_2795_, v___x_2644_, v_a_2794_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v_val_2692_);
return v___x_2796_;
}
else
{
lean_dec(v_val_2692_);
return v___x_2793_;
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
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec(v_stx_2294_);
v___x_2847_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec(v_stx_2294_);
v___x_2849_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_dec(v_stx_2294_);
v___x_2851_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2853_ = lean_unsigned_to_nat(2u);
v___x_2854_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2853_);
v___x_2855_ = l_Lean_Syntax_getArgs(v___x_2854_);
lean_dec(v___x_2854_);
v_sz_2856_ = lean_array_size(v___x_2855_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_2856_, v___x_2857_, v___x_2855_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v___x_2859_; lean_object* v_env_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2859_ = lean_st_ref_get(v_a_2300_);
v_env_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc_ref(v_env_2860_);
lean_dec(v___x_2859_);
v___x_2861_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2862_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2863_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2861_, v_env_2860_, v___x_2862_);
v___x_2864_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2865_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2863_, v___x_2864_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2896_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2896_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2896_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_fst_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2894_; 
v_fst_2870_ = lean_ctor_get(v_a_2866_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v_a_2866_, 1);
lean_dec(v_unused_2895_);
v___x_2872_ = v_a_2866_;
v_isShared_2873_ = v_isSharedCheck_2894_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_fst_2870_);
lean_dec(v_a_2866_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2894_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
if (lean_obj_tag(v_fst_2870_) == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
lean_del_object(v___x_2868_);
v___x_2874_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2875_ = l_Lean_MessageData_ofName(v___x_2862_);
lean_inc_ref(v___x_2875_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 7);
lean_ctor_set(v___x_2872_, 1, v___x_2875_);
lean_ctor_set(v___x_2872_, 0, v___x_2874_);
v___x_2877_ = v___x_2872_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2878_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2881_ = l_Lean_indentD(v___x_2880_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2879_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2875_);
v___x_2886_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
lean_inc_ref(v_a_2295_);
v___x_2888_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2887_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2888_;
}
}
else
{
lean_object* v_val_2890_; lean_object* v___x_2892_; 
lean_del_object(v___x_2872_);
lean_dec(v___x_2862_);
lean_dec(v_stx_2294_);
v_val_2890_ = lean_ctor_get(v_fst_2870_, 0);
lean_inc(v_val_2890_);
lean_dec_ref(v_fst_2870_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_val_2890_);
v___x_2892_ = v___x_2868_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_val_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v___x_2862_);
lean_dec(v_stx_2294_);
v_a_2897_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2865_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2865_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v_val_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_3039_; 
v_val_2905_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_2907_ = v___x_2858_;
v_isShared_2908_ = v_isSharedCheck_3039_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_val_2905_);
lean_dec(v___x_2858_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_3039_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_finSeq_x3f_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2909_);
v___x_2934_ = lean_unsigned_to_nat(3u);
v___x_2935_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_isNone(v___x_2935_);
if (v___x_2936_ == 0)
{
uint8_t v___x_2937_; 
lean_inc(v___x_2935_);
v___x_2937_ = l_Lean_Syntax_matchesNull(v___x_2935_, v___x_2909_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v_env_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v___x_2935_);
lean_dec(v___x_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_val_2905_);
v___x_2938_ = lean_st_ref_get(v_a_2300_);
v_env_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_ref(v_env_2939_);
lean_dec(v___x_2938_);
v___x_2940_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2941_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2942_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2940_, v_env_2939_, v___x_2941_);
v___x_2943_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2944_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2942_, v___x_2943_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2975_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2975_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2975_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_fst_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2973_; 
v_fst_2949_ = lean_ctor_get(v_a_2945_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_a_2945_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v_a_2945_, 1);
lean_dec(v_unused_2974_);
v___x_2951_ = v_a_2945_;
v_isShared_2952_ = v_isSharedCheck_2973_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_fst_2949_);
lean_dec(v_a_2945_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2973_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
if (lean_obj_tag(v_fst_2949_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_del_object(v___x_2947_);
v___x_2953_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2954_ = l_Lean_MessageData_ofName(v___x_2941_);
lean_inc_ref(v___x_2954_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 7);
lean_ctor_set(v___x_2951_, 1, v___x_2954_);
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2957_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2960_ = l_Lean_indentD(v___x_2959_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2958_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v___x_2954_);
v___x_2965_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
lean_inc_ref(v_a_2295_);
v___x_2967_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2966_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2967_;
}
}
else
{
lean_object* v_val_2969_; lean_object* v___x_2971_; 
lean_del_object(v___x_2951_);
lean_dec(v___x_2941_);
lean_dec(v_stx_2294_);
v_val_2969_ = lean_ctor_get(v_fst_2949_, 0);
lean_inc(v_val_2969_);
lean_dec_ref(v_fst_2949_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_val_2969_);
v___x_2971_ = v___x_2947_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_val_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v___x_2941_);
lean_dec(v_stx_2294_);
v_a_2976_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2944_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2944_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = l_Lean_Syntax_getArg(v___x_2935_, v___x_2984_);
lean_dec(v___x_2935_);
v___x_2986_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
lean_inc(v___x_2985_);
v___x_2987_ = l_Lean_Syntax_isOfKind(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v_env_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec(v___x_2985_);
lean_dec(v___x_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_val_2905_);
v___x_2988_ = lean_st_ref_get(v_a_2300_);
v_env_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc_ref(v_env_2989_);
lean_dec(v___x_2988_);
v___x_2990_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2991_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2992_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2990_, v_env_2989_, v___x_2991_);
v___x_2993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2994_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2992_, v___x_2993_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3025_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3025_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3025_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_fst_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3023_; 
v_fst_2999_ = lean_ctor_get(v_a_2995_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_a_2995_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v_a_2995_, 1);
lean_dec(v_unused_3024_);
v___x_3001_ = v_a_2995_;
v_isShared_3002_ = v_isSharedCheck_3023_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_fst_2999_);
lean_dec(v_a_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3023_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
if (lean_obj_tag(v_fst_2999_) == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_del_object(v___x_2997_);
v___x_3003_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3004_ = l_Lean_MessageData_ofName(v___x_2991_);
lean_inc_ref(v___x_3004_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 7);
lean_ctor_set(v___x_3001_, 1, v___x_3004_);
lean_ctor_set(v___x_3001_, 0, v___x_3003_);
v___x_3006_ = v___x_3001_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3010_ = l_Lean_indentD(v___x_3009_);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3008_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v___x_3004_);
v___x_3015_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
lean_inc_ref(v_a_2295_);
v___x_3017_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3016_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3017_;
}
}
else
{
lean_object* v_val_3019_; lean_object* v___x_3021_; 
lean_del_object(v___x_3001_);
lean_dec(v___x_2991_);
lean_dec(v_stx_2294_);
v_val_3019_ = lean_ctor_get(v_fst_2999_, 0);
lean_inc(v_val_3019_);
lean_dec_ref(v_fst_2999_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v_val_3019_);
v___x_3021_ = v___x_2997_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_val_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v___x_2991_);
lean_dec(v_stx_2294_);
v_a_3026_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2994_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2994_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_dec(v_stx_2294_);
v___x_3034_ = l_Lean_Syntax_getArg(v___x_2985_, v___x_2909_);
lean_dec(v___x_2985_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_3034_);
v___x_3036_ = v___x_2907_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
v_finSeq_x3f_2912_ = v___x_3036_;
v___y_2913_ = v_a_2295_;
v___y_2914_ = v_a_2296_;
v___y_2915_ = v_a_2297_;
v___y_2916_ = v_a_2298_;
v___y_2917_ = v_a_2299_;
v___y_2918_ = v_a_2300_;
goto v___jp_2911_;
}
}
}
}
else
{
lean_object* v___x_3038_; 
lean_dec(v___x_2935_);
lean_del_object(v___x_2907_);
lean_dec(v_stx_2294_);
v___x_3038_ = lean_box(0);
v_finSeq_x3f_2912_ = v___x_3038_;
v___y_2913_ = v_a_2295_;
v___y_2914_ = v_a_2296_;
v___y_2915_ = v_a_2297_;
v___y_2916_ = v_a_2298_;
v___y_2917_ = v_a_2299_;
v___y_2918_ = v_a_2300_;
goto v___jp_2911_;
}
v___jp_2911_:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2910_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; size_t v_sz_2921_; lean_object* v___x_2922_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v___x_2919_);
v_sz_2921_ = lean_array_size(v_val_2905_);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_2905_, v_sz_2921_, v___x_2857_, v_a_2920_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v_val_2905_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2933_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2933_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2933_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2929_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_2923_, v_a_2925_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2929_);
v___x_2931_ = v___x_2927_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
else
{
lean_dec(v_a_2923_);
return v___x_2924_;
}
}
else
{
lean_dec(v_finSeq_x3f_2912_);
return v___x_2922_;
}
}
else
{
lean_dec(v_finSeq_x3f_2912_);
lean_dec(v_val_2905_);
return v___x_2919_;
}
}
}
}
}
}
else
{
lean_object* v___x_3040_; lean_object* v___y_3042_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3040_ = lean_unsigned_to_nat(1u);
v___x_3113_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3040_);
v___x_3114_ = l_Lean_Syntax_getArgs(v___x_3113_);
lean_dec(v___x_3113_);
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3117_ = lean_array_get_size(v___x_3114_);
v___x_3118_ = lean_nat_dec_lt(v___x_3115_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3114_);
v___y_3042_ = v___x_3116_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = lean_box(v___x_2471_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v___x_3116_);
v___x_3121_ = lean_nat_dec_le(v___x_3117_, v___x_3117_);
if (v___x_3121_ == 0)
{
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3120_);
lean_dec_ref(v___x_3114_);
v___y_3042_ = v___x_3116_;
goto v___jp_3041_;
}
else
{
size_t v___x_3122_; size_t v___x_3123_; lean_object* v___x_3124_; lean_object* v_snd_3125_; 
v___x_3122_ = ((size_t)0ULL);
v___x_3123_ = lean_usize_of_nat(v___x_3117_);
v___x_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2471_, v___x_2469_, v___x_3114_, v___x_3122_, v___x_3123_, v___x_3120_);
lean_dec_ref(v___x_3114_);
v_snd_3125_ = lean_ctor_get(v___x_3124_, 1);
lean_inc(v_snd_3125_);
lean_dec_ref(v___x_3124_);
v___y_3042_ = v_snd_3125_;
goto v___jp_3041_;
}
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; lean_object* v_snd_3129_; 
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3117_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2471_, v___x_2469_, v___x_3114_, v___x_3126_, v___x_3127_, v___x_3120_);
lean_dec_ref(v___x_3114_);
v_snd_3129_ = lean_ctor_get(v___x_3128_, 1);
lean_inc(v_snd_3129_);
lean_dec_ref(v___x_3128_);
v___y_3042_ = v_snd_3129_;
goto v___jp_3041_;
}
}
v___jp_3041_:
{
size_t v_sz_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v_sz_3043_ = lean_array_size(v___y_3042_);
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3043_, v___x_3044_, v___y_3042_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3046_; lean_object* v_env_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3046_ = lean_st_ref_get(v_a_2300_);
v_env_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc_ref(v_env_3047_);
lean_dec(v___x_3046_);
v___x_3048_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3049_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3050_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3048_, v_env_3047_, v___x_3049_);
v___x_3051_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3052_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3050_, v___x_3051_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3083_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3083_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3083_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_fst_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3081_; 
v_fst_3057_ = lean_ctor_get(v_a_3053_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_a_3053_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v_a_3053_, 1);
lean_dec(v_unused_3082_);
v___x_3059_ = v_a_3053_;
v_isShared_3060_ = v_isSharedCheck_3081_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_fst_3057_);
lean_dec(v_a_3053_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3081_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
if (lean_obj_tag(v_fst_3057_) == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
lean_del_object(v___x_3055_);
v___x_3061_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3062_ = l_Lean_MessageData_ofName(v___x_3049_);
lean_inc_ref(v___x_3062_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set_tag(v___x_3059_, 7);
lean_ctor_set(v___x_3059_, 1, v___x_3062_);
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3064_ = v___x_3059_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3065_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3068_ = l_Lean_indentD(v___x_3067_);
v___x_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3066_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3062_);
v___x_3073_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
lean_inc_ref(v_a_2295_);
v___x_3075_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3074_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3075_;
}
}
else
{
lean_object* v_val_3077_; lean_object* v___x_3079_; 
lean_del_object(v___x_3059_);
lean_dec(v___x_3049_);
lean_dec(v_stx_2294_);
v_val_3077_ = lean_ctor_get(v_fst_3057_, 0);
lean_inc(v_val_3077_);
lean_dec_ref(v_fst_3057_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v_val_3077_);
v___x_3079_ = v___x_3055_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_val_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v___x_3049_);
lean_dec(v_stx_2294_);
v_a_3084_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3052_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3052_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref(v___x_3045_);
v___x_3092_ = lean_unsigned_to_nat(3u);
v___x_3093_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3092_);
lean_dec(v_stx_2294_);
v___x_3094_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3093_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3112_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3112_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3112_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint8_t v_returnsEarly_3099_; lean_object* v_reassigns_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3110_; 
v_returnsEarly_3099_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*2 + 2);
v_reassigns_3100_ = lean_ctor_get(v_a_3095_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_a_3095_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v_a_3095_, 0);
lean_dec(v_unused_3111_);
v___x_3102_ = v_a_3095_;
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_reassigns_3100_);
lean_dec(v_a_3095_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3040_);
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_reassigns_3100_);
lean_ctor_set_uint8(v_reuseFailAlloc_3109_, sizeof(void*)*2 + 2, v_returnsEarly_3099_);
v___x_3105_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3107_; 
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*2, v___x_2469_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*2 + 1, v___x_2469_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3105_);
v___x_3107_ = v___x_3097_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
else
{
return v___x_3094_;
}
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3130_ = lean_unsigned_to_nat(1u);
v___x_3131_ = lean_unsigned_to_nat(3u);
v___x_3132_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3131_);
lean_dec(v_stx_2294_);
v___x_3133_ = l_Lean_NameSet_empty;
v___x_3134_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3134_, 0, v___x_3130_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*2, v___x_2467_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*2 + 1, v___x_2467_);
lean_ctor_set_uint8(v___x_3134_, sizeof(void*)*2 + 2, v___x_2467_);
v___x_3135_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3132_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3134_, v_a_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_dec_ref(v___x_3134_);
return v___x_3135_;
}
}
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; size_t v_sz_3148_; size_t v___x_3149_; lean_object* v___x_3150_; 
v___x_3145_ = lean_unsigned_to_nat(4u);
v___x_3146_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3145_);
v___x_3147_ = l_Lean_Syntax_getArgs(v___x_3146_);
lean_dec(v___x_3146_);
v_sz_3148_ = lean_array_size(v___x_3147_);
v___x_3149_ = ((size_t)0ULL);
v___x_3150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3148_, v___x_3149_, v___x_3147_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v___x_3151_; lean_object* v_env_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3151_ = lean_st_ref_get(v_a_2300_);
v_env_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_ref(v_env_3152_);
lean_dec(v___x_3151_);
v___x_3153_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3154_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3155_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3153_, v_env_3152_, v___x_3154_);
v___x_3156_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3157_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3155_, v___x_3156_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3188_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3188_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3188_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_fst_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3186_; 
v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_a_3158_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; 
v_unused_3187_ = lean_ctor_get(v_a_3158_, 1);
lean_dec(v_unused_3187_);
v___x_3164_ = v_a_3158_;
v_isShared_3165_ = v_isSharedCheck_3186_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_fst_3162_);
lean_dec(v_a_3158_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3186_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
if (lean_obj_tag(v_fst_3162_) == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
lean_del_object(v___x_3160_);
v___x_3166_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3167_ = l_Lean_MessageData_ofName(v___x_3154_);
lean_inc_ref(v___x_3167_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 7);
lean_ctor_set(v___x_3164_, 1, v___x_3167_);
lean_ctor_set(v___x_3164_, 0, v___x_3166_);
v___x_3169_ = v___x_3164_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3170_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3173_ = l_Lean_indentD(v___x_3172_);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3171_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3167_);
v___x_3178_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
lean_inc_ref(v_a_2295_);
v___x_3180_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3179_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3180_;
}
}
else
{
lean_object* v_val_3182_; lean_object* v___x_3184_; 
lean_del_object(v___x_3164_);
lean_dec(v___x_3154_);
lean_dec(v_stx_2294_);
v_val_3182_ = lean_ctor_get(v_fst_3162_, 0);
lean_inc(v_val_3182_);
lean_dec_ref(v_fst_3162_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v_val_3182_);
v___x_3184_ = v___x_3160_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_val_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v___x_3154_);
lean_dec(v_stx_2294_);
v_a_3189_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3157_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3157_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3284_; 
v_val_3197_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3199_ = v___x_3150_;
v_isShared_3200_ = v_isSharedCheck_3284_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_val_3197_);
lean_dec(v___x_3150_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3284_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_elseSeq_x3f_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3201_ = lean_unsigned_to_nat(3u);
v___x_3202_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3201_);
v___x_3227_ = lean_unsigned_to_nat(5u);
v___x_3228_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3227_);
v___x_3229_ = l_Lean_Syntax_isNone(v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3228_);
v___x_3231_ = l_Lean_Syntax_matchesNull(v___x_3228_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v_env_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec(v___x_3228_);
lean_dec(v___x_3202_);
lean_del_object(v___x_3199_);
lean_dec(v_val_3197_);
v___x_3232_ = lean_st_ref_get(v_a_2300_);
v_env_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc_ref(v_env_3233_);
lean_dec(v___x_3232_);
v___x_3234_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3235_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3236_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3234_, v_env_3233_, v___x_3235_);
v___x_3237_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3238_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3236_, v___x_3237_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3269_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3269_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3269_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v_fst_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3267_; 
v_fst_3243_ = lean_ctor_get(v_a_3239_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_a_3239_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_a_3239_, 1);
lean_dec(v_unused_3268_);
v___x_3245_ = v_a_3239_;
v_isShared_3246_ = v_isSharedCheck_3267_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_fst_3243_);
lean_dec(v_a_3239_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3267_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
if (lean_obj_tag(v_fst_3243_) == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
lean_del_object(v___x_3241_);
v___x_3247_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3248_ = l_Lean_MessageData_ofName(v___x_3235_);
lean_inc_ref(v___x_3248_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set_tag(v___x_3245_, 7);
lean_ctor_set(v___x_3245_, 1, v___x_3248_);
lean_ctor_set(v___x_3245_, 0, v___x_3247_);
v___x_3250_ = v___x_3245_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3251_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3254_ = l_Lean_indentD(v___x_3253_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3252_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___x_3248_);
v___x_3259_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
lean_inc_ref(v_a_2295_);
v___x_3261_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3260_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3261_;
}
}
else
{
lean_object* v_val_3263_; lean_object* v___x_3265_; 
lean_del_object(v___x_3245_);
lean_dec(v___x_3235_);
lean_dec(v_stx_2294_);
v_val_3263_ = lean_ctor_get(v_fst_3243_, 0);
lean_inc(v_val_3263_);
lean_dec_ref(v_fst_3243_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v_val_3263_);
v___x_3265_ = v___x_3241_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_val_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v___x_3235_);
lean_dec(v_stx_2294_);
v_a_3270_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3238_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3238_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_dec(v_stx_2294_);
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = l_Lean_Syntax_getArg(v___x_3228_, v___x_3278_);
lean_dec(v___x_3228_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3279_);
v___x_3281_ = v___x_3199_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
v_elseSeq_x3f_3204_ = v___x_3281_;
v___y_3205_ = v_a_2295_;
v___y_3206_ = v_a_2296_;
v___y_3207_ = v_a_2297_;
v___y_3208_ = v_a_2298_;
v___y_3209_ = v_a_2299_;
v___y_3210_ = v_a_2300_;
goto v___jp_3203_;
}
}
}
else
{
lean_object* v___x_3283_; 
lean_dec(v___x_3228_);
lean_del_object(v___x_3199_);
lean_dec(v_stx_2294_);
v___x_3283_ = lean_box(0);
v_elseSeq_x3f_3204_ = v___x_3283_;
v___y_3205_ = v_a_2295_;
v___y_3206_ = v_a_2296_;
v___y_3207_ = v_a_2297_;
v___y_3208_ = v_a_2298_;
v___y_3209_ = v_a_2299_;
v___y_3210_ = v_a_2300_;
goto v___jp_3203_;
}
v___jp_3203_:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; size_t v_sz_3214_; lean_object* v___x_3215_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___x_3211_);
v___x_3213_ = l_Array_reverse___redArg(v_val_3197_);
v_sz_3214_ = lean_array_size(v___x_3213_);
v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3213_, v_sz_3214_, v___x_3149_, v_a_3212_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v___x_3213_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref(v___x_3215_);
v___x_3217_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3202_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3226_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3218_, v_a_3216_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3222_);
v___x_3224_ = v___x_3220_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
lean_dec(v_a_3216_);
return v___x_3217_;
}
}
else
{
lean_dec(v___x_3202_);
return v___x_3215_;
}
}
else
{
lean_dec(v___x_3202_);
lean_dec(v_val_3197_);
return v___x_3211_;
}
}
}
}
}
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = lean_unsigned_to_nat(1u);
v___x_3457_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3286_);
v___x_3458_ = l_Lean_Syntax_isNone(v___x_3457_);
if (v___x_3458_ == 0)
{
uint8_t v___x_3459_; 
lean_inc(v___x_3457_);
v___x_3459_ = l_Lean_Syntax_matchesNull(v___x_3457_, v___x_3286_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v_env_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec(v___x_3457_);
v___x_3460_ = lean_st_ref_get(v_a_2300_);
v_env_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc_ref(v_env_3461_);
lean_dec(v___x_3460_);
v___x_3462_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3463_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3464_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3462_, v_env_3461_, v___x_3463_);
v___x_3465_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3466_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3464_, v___x_3465_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3497_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3497_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3497_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_fst_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3495_; 
v_fst_3471_ = lean_ctor_get(v_a_3467_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v_a_3467_, 1);
lean_dec(v_unused_3496_);
v___x_3473_ = v_a_3467_;
v_isShared_3474_ = v_isSharedCheck_3495_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_fst_3471_);
lean_dec(v_a_3467_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3495_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
if (lean_obj_tag(v_fst_3471_) == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_del_object(v___x_3469_);
v___x_3475_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3476_ = l_Lean_MessageData_ofName(v___x_3463_);
lean_inc_ref(v___x_3476_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 7);
lean_ctor_set(v___x_3473_, 1, v___x_3476_);
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3478_ = v___x_3473_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3479_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3482_ = l_Lean_indentD(v___x_3481_);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3480_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___x_3476_);
v___x_3487_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3486_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
lean_inc_ref(v_a_2295_);
v___x_3489_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3488_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3489_;
}
}
else
{
lean_object* v_val_3491_; lean_object* v___x_3493_; 
lean_del_object(v___x_3473_);
lean_dec(v___x_3463_);
lean_dec(v_stx_2294_);
v_val_3491_ = lean_ctor_get(v_fst_3471_, 0);
lean_inc(v_val_3491_);
lean_dec_ref(v_fst_3471_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v_val_3491_);
v___x_3493_ = v___x_3469_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_val_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v___x_3463_);
lean_dec(v_stx_2294_);
v_a_3498_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3466_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3466_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3506_ = l_Lean_Syntax_getArg(v___x_3457_, v___x_3285_);
lean_dec(v___x_3457_);
v___x_3507_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67));
v___x_3508_ = l_Lean_Syntax_isOfKind(v___x_3506_, v___x_3507_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v_env_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3509_ = lean_st_ref_get(v_a_2300_);
v_env_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc_ref(v_env_3510_);
lean_dec(v___x_3509_);
v___x_3511_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3512_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3513_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3511_, v_env_3510_, v___x_3512_);
v___x_3514_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3515_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3513_, v___x_3514_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3546_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3546_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3546_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v_fst_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3544_; 
v_fst_3520_ = lean_ctor_get(v_a_3516_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; 
v_unused_3545_ = lean_ctor_get(v_a_3516_, 1);
lean_dec(v_unused_3545_);
v___x_3522_ = v_a_3516_;
v_isShared_3523_ = v_isSharedCheck_3544_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_fst_3520_);
lean_dec(v_a_3516_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3544_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
if (lean_obj_tag(v_fst_3520_) == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
lean_del_object(v___x_3518_);
v___x_3524_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3525_ = l_Lean_MessageData_ofName(v___x_3512_);
lean_inc_ref(v___x_3525_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set_tag(v___x_3522_, 7);
lean_ctor_set(v___x_3522_, 1, v___x_3525_);
lean_ctor_set(v___x_3522_, 0, v___x_3524_);
v___x_3527_ = v___x_3522_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3528_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3531_ = l_Lean_indentD(v___x_3530_);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3529_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v___x_3525_);
v___x_3536_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
lean_inc_ref(v_a_2295_);
v___x_3538_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3537_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3538_;
}
}
else
{
lean_object* v_val_3540_; lean_object* v___x_3542_; 
lean_del_object(v___x_3522_);
lean_dec(v___x_3512_);
lean_dec(v_stx_2294_);
v_val_3540_ = lean_ctor_get(v_fst_3520_, 0);
lean_inc(v_val_3540_);
lean_dec_ref(v_fst_3520_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_val_3540_);
v___x_3542_ = v___x_3518_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_val_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v___x_3512_);
lean_dec(v_stx_2294_);
v_a_3547_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3515_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3515_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
v___y_3352_ = v_a_2295_;
v___y_3353_ = v_a_2296_;
v___y_3354_ = v_a_2297_;
v___y_3355_ = v_a_2298_;
v___y_3356_ = v_a_2299_;
v___y_3357_ = v_a_2300_;
goto v___jp_3351_;
}
}
}
else
{
lean_dec(v___x_3457_);
v___y_3352_ = v_a_2295_;
v___y_3353_ = v_a_2296_;
v___y_3354_ = v_a_2297_;
v___y_3355_ = v_a_2298_;
v___y_3356_ = v_a_2299_;
v___y_3357_ = v_a_2300_;
goto v___jp_3351_;
}
v___jp_3287_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3294_ = lean_unsigned_to_nat(6u);
v___x_3295_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3294_);
v___x_3296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3295_);
v___x_3297_ = l_Lean_Syntax_isOfKind(v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v_env_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v___x_3295_);
v___x_3298_ = lean_st_ref_get(v___y_3293_);
v_env_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_ref(v_env_3299_);
lean_dec(v___x_3298_);
v___x_3300_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3301_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3302_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3300_, v_env_3299_, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3304_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3302_, v___x_3303_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3335_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3335_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3335_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v_fst_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3333_; 
v_fst_3309_ = lean_ctor_get(v_a_3305_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_a_3305_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_a_3305_, 1);
lean_dec(v_unused_3334_);
v___x_3311_ = v_a_3305_;
v_isShared_3312_ = v_isSharedCheck_3333_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_fst_3309_);
lean_dec(v_a_3305_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3333_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
if (lean_obj_tag(v_fst_3309_) == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
lean_del_object(v___x_3307_);
v___x_3313_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3314_ = l_Lean_MessageData_ofName(v___x_3301_);
lean_inc_ref(v___x_3314_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set_tag(v___x_3311_, 7);
lean_ctor_set(v___x_3311_, 1, v___x_3314_);
lean_ctor_set(v___x_3311_, 0, v___x_3313_);
v___x_3316_ = v___x_3311_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3317_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3320_ = l_Lean_indentD(v___x_3319_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3318_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3314_);
v___x_3325_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
lean_inc_ref(v___y_3288_);
v___x_3327_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3326_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3327_;
}
}
else
{
lean_object* v_val_3329_; lean_object* v___x_3331_; 
lean_del_object(v___x_3311_);
lean_dec(v___x_3301_);
lean_dec(v_stx_2294_);
v_val_3329_ = lean_ctor_get(v_fst_3309_, 0);
lean_inc(v_val_3329_);
lean_dec_ref(v_fst_3309_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v_val_3329_);
v___x_3331_ = v___x_3307_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_val_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v___x_3301_);
lean_dec(v_stx_2294_);
v_a_3336_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3304_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3304_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; size_t v_sz_3348_; size_t v___x_3349_; lean_object* v___x_3350_; 
lean_dec(v_stx_2294_);
v___x_3344_ = l_Lean_Syntax_getArg(v___x_3295_, v___x_3285_);
lean_dec(v___x_3295_);
v___x_3345_ = l_Lean_Syntax_getArgs(v___x_3344_);
lean_dec(v___x_3344_);
v___x_3346_ = l_Lean_NameSet_empty;
v___x_3347_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3347_, 0, v___x_3286_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*2, v___x_2463_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*2 + 1, v___x_2463_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*2 + 2, v___x_2463_);
v_sz_3348_ = lean_array_size(v___x_3345_);
v___x_3349_ = ((size_t)0ULL);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2463_, v___x_3345_, v_sz_3348_, v___x_3349_, v___x_3347_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec_ref(v___x_3345_);
return v___x_3350_;
}
}
v___jp_3351_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3358_ = lean_unsigned_to_nat(2u);
v___x_3359_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3358_);
v___x_3360_ = l_Lean_Syntax_isNone(v___x_3359_);
if (v___x_3360_ == 0)
{
uint8_t v___x_3361_; 
lean_inc(v___x_3359_);
v___x_3361_ = l_Lean_Syntax_matchesNull(v___x_3359_, v___x_3286_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v_env_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v___x_3359_);
v___x_3362_ = lean_st_ref_get(v___y_3357_);
v_env_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc_ref(v_env_3363_);
lean_dec(v___x_3362_);
v___x_3364_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3365_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3366_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3364_, v_env_3363_, v___x_3365_);
v___x_3367_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3368_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3366_, v___x_3367_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3399_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3399_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3399_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v_fst_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3397_; 
v_fst_3373_ = lean_ctor_get(v_a_3369_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3369_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v_a_3369_, 1);
lean_dec(v_unused_3398_);
v___x_3375_ = v_a_3369_;
v_isShared_3376_ = v_isSharedCheck_3397_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_fst_3373_);
lean_dec(v_a_3369_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3397_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
if (lean_obj_tag(v_fst_3373_) == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
lean_del_object(v___x_3371_);
v___x_3377_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3378_ = l_Lean_MessageData_ofName(v___x_3365_);
lean_inc_ref(v___x_3378_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 7);
lean_ctor_set(v___x_3375_, 1, v___x_3378_);
lean_ctor_set(v___x_3375_, 0, v___x_3377_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3381_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3384_ = l_Lean_indentD(v___x_3383_);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3382_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___x_3378_);
v___x_3389_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
lean_inc_ref(v___y_3352_);
v___x_3391_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3390_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
return v___x_3391_;
}
}
else
{
lean_object* v_val_3393_; lean_object* v___x_3395_; 
lean_del_object(v___x_3375_);
lean_dec(v___x_3365_);
lean_dec(v_stx_2294_);
v_val_3393_ = lean_ctor_get(v_fst_3373_, 0);
lean_inc(v_val_3393_);
lean_dec_ref(v_fst_3373_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v_val_3393_);
v___x_3395_ = v___x_3371_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_val_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v___x_3365_);
lean_dec(v_stx_2294_);
v_a_3400_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3368_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3368_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3408_ = l_Lean_Syntax_getArg(v___x_3359_, v___x_3285_);
lean_dec(v___x_3359_);
v___x_3409_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65));
v___x_3410_ = l_Lean_Syntax_isOfKind(v___x_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v_env_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3411_ = lean_st_ref_get(v___y_3357_);
v_env_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc_ref(v_env_3412_);
lean_dec(v___x_3411_);
v___x_3413_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3414_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3415_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3413_, v_env_3412_, v___x_3414_);
v___x_3416_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3417_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3415_, v___x_3416_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3448_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3448_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3448_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_fst_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3446_; 
v_fst_3422_ = lean_ctor_get(v_a_3418_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_a_3418_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; 
v_unused_3447_ = lean_ctor_get(v_a_3418_, 1);
lean_dec(v_unused_3447_);
v___x_3424_ = v_a_3418_;
v_isShared_3425_ = v_isSharedCheck_3446_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_fst_3422_);
lean_dec(v_a_3418_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3446_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
if (lean_obj_tag(v_fst_3422_) == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
lean_del_object(v___x_3420_);
v___x_3426_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3427_ = l_Lean_MessageData_ofName(v___x_3414_);
lean_inc_ref(v___x_3427_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 7);
lean_ctor_set(v___x_3424_, 1, v___x_3427_);
lean_ctor_set(v___x_3424_, 0, v___x_3426_);
v___x_3429_ = v___x_3424_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3430_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3433_ = l_Lean_indentD(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3431_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3434_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v___x_3427_);
v___x_3438_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
lean_inc_ref(v___y_3352_);
v___x_3440_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3439_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
return v___x_3440_;
}
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3444_; 
lean_del_object(v___x_3424_);
lean_dec(v___x_3414_);
lean_dec(v_stx_2294_);
v_val_3442_ = lean_ctor_get(v_fst_3422_, 0);
lean_inc(v_val_3442_);
lean_dec_ref(v_fst_3422_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v_val_3442_);
v___x_3444_ = v___x_3420_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_val_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v___x_3414_);
lean_dec(v_stx_2294_);
v_a_3449_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3417_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3417_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
v___y_3288_ = v___y_3352_;
v___y_3289_ = v___y_3353_;
v___y_3290_ = v___y_3354_;
v___y_3291_ = v___y_3355_;
v___y_3292_ = v___y_3356_;
v___y_3293_ = v___y_3357_;
goto v___jp_3287_;
}
}
}
else
{
lean_dec(v___x_3359_);
v___y_3288_ = v___y_3352_;
v___y_3289_ = v___y_3353_;
v___y_3290_ = v___y_3354_;
v___y_3291_ = v___y_3355_;
v___y_3292_ = v___y_3356_;
v___y_3293_ = v___y_3357_;
goto v___jp_3287_;
}
}
}
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3555_);
v___x_3557_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3556_);
v___x_3558_ = l_Lean_Syntax_isOfKind(v___x_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3559_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3556_);
v___x_3560_ = l_Lean_Syntax_isOfKind(v___x_3556_, v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v_env_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec(v___x_3556_);
v___x_3561_ = lean_st_ref_get(v_a_2300_);
v_env_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc_ref(v_env_3562_);
lean_dec(v___x_3561_);
v___x_3563_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3564_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3565_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3563_, v_env_3562_, v___x_3564_);
v___x_3566_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3567_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3565_, v___x_3566_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3598_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3598_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3598_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_fst_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3596_; 
v_fst_3572_ = lean_ctor_get(v_a_3568_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3568_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v_a_3568_, 1);
lean_dec(v_unused_3597_);
v___x_3574_ = v_a_3568_;
v_isShared_3575_ = v_isSharedCheck_3596_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_fst_3572_);
lean_dec(v_a_3568_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3596_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
if (lean_obj_tag(v_fst_3572_) == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_del_object(v___x_3570_);
v___x_3576_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3577_ = l_Lean_MessageData_ofName(v___x_3564_);
lean_inc_ref(v___x_3577_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 7);
lean_ctor_set(v___x_3574_, 1, v___x_3577_);
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3580_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3583_ = l_Lean_indentD(v___x_3582_);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3581_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v___x_3577_);
v___x_3588_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
lean_inc_ref(v_a_2295_);
v___x_3590_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3589_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3590_;
}
}
else
{
lean_object* v_val_3592_; lean_object* v___x_3594_; 
lean_del_object(v___x_3574_);
lean_dec(v___x_3564_);
lean_dec(v_stx_2294_);
v_val_3592_ = lean_ctor_get(v_fst_3572_, 0);
lean_inc(v_val_3592_);
lean_dec_ref(v_fst_3572_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v_val_3592_);
v___x_3594_ = v___x_3570_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_val_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v___x_3564_);
lean_dec(v_stx_2294_);
v_a_3599_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3567_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3567_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v_stx_2294_);
v___x_3607_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2431_, v___x_3556_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3607_;
}
}
else
{
lean_object* v___x_3608_; 
lean_dec(v_stx_2294_);
v___x_3608_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2431_, v___x_3556_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3608_;
}
}
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3609_);
v___x_3611_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69));
lean_inc(v___x_3610_);
v___x_3612_ = l_Lean_Syntax_isOfKind(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71));
lean_inc(v___x_3610_);
v___x_3614_ = l_Lean_Syntax_isOfKind(v___x_3610_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v_env_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_dec(v___x_3610_);
v___x_3615_ = lean_st_ref_get(v_a_2300_);
v_env_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc_ref(v_env_3616_);
lean_dec(v___x_3615_);
v___x_3617_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3618_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3619_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3617_, v_env_3616_, v___x_3618_);
v___x_3620_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3621_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3619_, v___x_3620_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3652_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3652_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3652_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v_fst_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3650_; 
v_fst_3626_ = lean_ctor_get(v_a_3622_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_a_3622_);
if (v_isSharedCheck_3650_ == 0)
{
lean_object* v_unused_3651_; 
v_unused_3651_ = lean_ctor_get(v_a_3622_, 1);
lean_dec(v_unused_3651_);
v___x_3628_ = v_a_3622_;
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_fst_3626_);
lean_dec(v_a_3622_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
if (lean_obj_tag(v_fst_3626_) == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
lean_del_object(v___x_3624_);
v___x_3630_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3631_ = l_Lean_MessageData_ofName(v___x_3618_);
lean_inc_ref(v___x_3631_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 7);
lean_ctor_set(v___x_3628_, 1, v___x_3631_);
lean_ctor_set(v___x_3628_, 0, v___x_3630_);
v___x_3633_ = v___x_3628_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3634_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3637_ = l_Lean_indentD(v___x_3636_);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3635_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v___x_3631_);
v___x_3642_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
lean_inc_ref(v_a_2295_);
v___x_3644_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3643_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3644_;
}
}
else
{
lean_object* v_val_3646_; lean_object* v___x_3648_; 
lean_del_object(v___x_3628_);
lean_dec(v___x_3618_);
lean_dec(v_stx_2294_);
v_val_3646_ = lean_ctor_get(v_fst_3626_, 0);
lean_inc(v_val_3646_);
lean_dec_ref(v_fst_3626_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v_val_3646_);
v___x_3648_ = v___x_3624_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_val_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v___x_3618_);
lean_dec(v_stx_2294_);
v_a_3653_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3621_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3621_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v___x_3661_; 
lean_dec(v_stx_2294_);
v___x_3661_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3610_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v___x_3610_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = lean_box(0);
v___x_3664_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3662_, v___x_3663_, v___x_3663_, v___x_3663_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3664_;
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3661_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3661_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
else
{
lean_object* v___x_3673_; 
lean_dec(v_stx_2294_);
v___x_3673_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3610_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v___x_3610_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = lean_box(0);
v___x_3676_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3674_, v___x_3675_, v___x_3675_, v___x_3675_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3676_;
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3673_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3673_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3685_ = lean_unsigned_to_nat(1u);
v___x_3686_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3685_);
v___x_3687_ = l_Lean_Syntax_isNone(v___x_3686_);
if (v___x_3687_ == 0)
{
uint8_t v___x_3688_; 
v___x_3688_ = l_Lean_Syntax_matchesNull(v___x_3686_, v___x_3685_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v_env_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3689_ = lean_st_ref_get(v_a_2300_);
v_env_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc_ref(v_env_3690_);
lean_dec(v___x_3689_);
v___x_3691_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3692_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3693_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3691_, v_env_3690_, v___x_3692_);
v___x_3694_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3695_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3693_, v___x_3694_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3726_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3726_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3726_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v_fst_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3724_; 
v_fst_3700_ = lean_ctor_get(v_a_3696_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_a_3696_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v_a_3696_, 1);
lean_dec(v_unused_3725_);
v___x_3702_ = v_a_3696_;
v_isShared_3703_ = v_isSharedCheck_3724_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_fst_3700_);
lean_dec(v_a_3696_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3724_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
if (lean_obj_tag(v_fst_3700_) == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
lean_del_object(v___x_3698_);
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3705_ = l_Lean_MessageData_ofName(v___x_3692_);
lean_inc_ref(v___x_3705_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set_tag(v___x_3702_, 7);
lean_ctor_set(v___x_3702_, 1, v___x_3705_);
lean_ctor_set(v___x_3702_, 0, v___x_3704_);
v___x_3707_ = v___x_3702_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3708_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3711_ = l_Lean_indentD(v___x_3710_);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3709_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___x_3705_);
v___x_3716_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
lean_inc_ref(v_a_2295_);
v___x_3718_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3717_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3718_;
}
}
else
{
lean_object* v_val_3720_; lean_object* v___x_3722_; 
lean_del_object(v___x_3702_);
lean_dec(v___x_3692_);
lean_dec(v_stx_2294_);
v_val_3720_ = lean_ctor_get(v_fst_3700_, 0);
lean_inc(v_val_3720_);
lean_dec_ref(v_fst_3700_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v_val_3720_);
v___x_3722_ = v___x_3698_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_val_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v___x_3692_);
lean_dec(v_stx_2294_);
v_a_3727_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3695_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3695_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
v___y_2449_ = v_a_2295_;
v___y_2450_ = v_a_2296_;
v___y_2451_ = v_a_2297_;
v___y_2452_ = v_a_2298_;
v___y_2453_ = v_a_2299_;
v___y_2454_ = v_a_2300_;
goto v___jp_2448_;
}
}
else
{
lean_dec(v___x_3686_);
v___y_2449_ = v_a_2295_;
v___y_2450_ = v_a_2296_;
v___y_2451_ = v_a_2297_;
v___y_2452_ = v_a_2298_;
v___y_2453_ = v_a_2299_;
v___y_2454_ = v_a_2300_;
goto v___jp_2448_;
}
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3735_);
v___x_3737_ = l_Lean_Syntax_isNone(v___x_3736_);
if (v___x_3737_ == 0)
{
uint8_t v___x_3738_; 
v___x_3738_ = l_Lean_Syntax_matchesNull(v___x_3736_, v___x_3735_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; lean_object* v_env_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3739_ = lean_st_ref_get(v_a_2300_);
v_env_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc_ref(v_env_3740_);
lean_dec(v___x_3739_);
v___x_3741_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3742_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3743_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3741_, v_env_3740_, v___x_3742_);
v___x_3744_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3745_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3743_, v___x_3744_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3776_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3776_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3776_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_fst_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3774_; 
v_fst_3750_ = lean_ctor_get(v_a_3746_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_a_3746_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v_a_3746_, 1);
lean_dec(v_unused_3775_);
v___x_3752_ = v_a_3746_;
v_isShared_3753_ = v_isSharedCheck_3774_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_fst_3750_);
lean_dec(v_a_3746_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3774_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
if (lean_obj_tag(v_fst_3750_) == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_del_object(v___x_3748_);
v___x_3754_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3755_ = l_Lean_MessageData_ofName(v___x_3742_);
lean_inc_ref(v___x_3755_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set_tag(v___x_3752_, 7);
lean_ctor_set(v___x_3752_, 1, v___x_3755_);
lean_ctor_set(v___x_3752_, 0, v___x_3754_);
v___x_3757_ = v___x_3752_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3758_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3761_ = l_Lean_indentD(v___x_3760_);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3759_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v___x_3755_);
v___x_3766_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
lean_inc_ref(v_a_2295_);
v___x_3768_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3767_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3768_;
}
}
else
{
lean_object* v_val_3770_; lean_object* v___x_3772_; 
lean_del_object(v___x_3752_);
lean_dec(v___x_3742_);
lean_dec(v_stx_2294_);
v_val_3770_ = lean_ctor_get(v_fst_3750_, 0);
lean_inc(v_val_3770_);
lean_dec_ref(v_fst_3750_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v_val_3770_);
v___x_3772_ = v___x_3748_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_val_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v___x_3742_);
lean_dec(v_stx_2294_);
v_a_3777_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3745_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3745_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
v___y_2316_ = v_a_2295_;
v___y_2317_ = v_a_2296_;
v___y_2318_ = v_a_2297_;
v___y_2319_ = v_a_2298_;
v___y_2320_ = v_a_2299_;
v___y_2321_ = v_a_2300_;
goto v___jp_2315_;
}
}
else
{
lean_dec(v___x_3736_);
v___y_2316_ = v_a_2295_;
v___y_2317_ = v_a_2296_;
v___y_2318_ = v_a_2297_;
v___y_2319_ = v_a_2298_;
v___y_2320_ = v_a_2299_;
v___y_2321_ = v_a_2300_;
goto v___jp_2315_;
}
}
v___jp_2448_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_unsigned_to_nat(2u);
v___x_2456_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2455_);
lean_dec(v_stx_2294_);
v___x_2457_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2447_, v___x_2456_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2457_;
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3785_);
v___x_3787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3788_ = l_Lean_Syntax_isOfKind(v___x_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v_env_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3789_ = lean_st_ref_get(v_a_2300_);
v_env_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc_ref(v_env_3790_);
lean_dec(v___x_3789_);
v___x_3791_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3792_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3793_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3791_, v_env_3790_, v___x_3792_);
v___x_3794_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3795_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3793_, v___x_3794_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3826_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3826_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3826_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v_fst_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3824_; 
v_fst_3800_ = lean_ctor_get(v_a_3796_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3796_);
if (v_isSharedCheck_3824_ == 0)
{
lean_object* v_unused_3825_; 
v_unused_3825_ = lean_ctor_get(v_a_3796_, 1);
lean_dec(v_unused_3825_);
v___x_3802_ = v_a_3796_;
v_isShared_3803_ = v_isSharedCheck_3824_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_fst_3800_);
lean_dec(v_a_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3824_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
if (lean_obj_tag(v_fst_3800_) == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
lean_del_object(v___x_3798_);
v___x_3804_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3805_ = l_Lean_MessageData_ofName(v___x_3792_);
lean_inc_ref(v___x_3805_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 7);
lean_ctor_set(v___x_3802_, 1, v___x_3805_);
lean_ctor_set(v___x_3802_, 0, v___x_3804_);
v___x_3807_ = v___x_3802_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3808_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3811_ = l_Lean_indentD(v___x_3810_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3809_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___x_3805_);
v___x_3816_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
lean_inc_ref(v_a_2295_);
v___x_3818_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3817_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3818_;
}
}
else
{
lean_object* v_val_3820_; lean_object* v___x_3822_; 
lean_del_object(v___x_3802_);
lean_dec(v___x_3792_);
lean_dec(v_stx_2294_);
v_val_3820_ = lean_ctor_get(v_fst_3800_, 0);
lean_inc(v_val_3820_);
lean_dec_ref(v_fst_3800_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v_val_3820_);
v___x_3822_ = v___x_3798_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_val_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec(v___x_3792_);
lean_dec(v_stx_2294_);
v_a_3827_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3795_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3795_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3835_);
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73));
lean_inc(v___x_3836_);
v___x_3838_ = l_Lean_Syntax_isOfKind(v___x_3836_, v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v_env_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec(v___x_3836_);
v___x_3839_ = lean_st_ref_get(v_a_2300_);
v_env_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc_ref(v_env_3840_);
lean_dec(v___x_3839_);
v___x_3841_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3842_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3843_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3841_, v_env_3840_, v___x_3842_);
v___x_3844_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3845_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3843_, v___x_3844_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3876_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3848_ = v___x_3845_;
v_isShared_3849_ = v_isSharedCheck_3876_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3876_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v_fst_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3874_; 
v_fst_3850_ = lean_ctor_get(v_a_3846_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_a_3846_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; 
v_unused_3875_ = lean_ctor_get(v_a_3846_, 1);
lean_dec(v_unused_3875_);
v___x_3852_ = v_a_3846_;
v_isShared_3853_ = v_isSharedCheck_3874_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_fst_3850_);
lean_dec(v_a_3846_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3874_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
if (lean_obj_tag(v_fst_3850_) == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3857_; 
lean_del_object(v___x_3848_);
v___x_3854_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3855_ = l_Lean_MessageData_ofName(v___x_3842_);
lean_inc_ref(v___x_3855_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set_tag(v___x_3852_, 7);
lean_ctor_set(v___x_3852_, 1, v___x_3855_);
lean_ctor_set(v___x_3852_, 0, v___x_3854_);
v___x_3857_ = v___x_3852_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3858_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3861_ = l_Lean_indentD(v___x_3860_);
v___x_3862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3859_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3862_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___x_3865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v___x_3855_);
v___x_3866_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3865_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
lean_inc_ref(v_a_2295_);
v___x_3868_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3867_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3868_;
}
}
else
{
lean_object* v_val_3870_; lean_object* v___x_3872_; 
lean_del_object(v___x_3852_);
lean_dec(v___x_3842_);
lean_dec(v_stx_2294_);
v_val_3870_ = lean_ctor_get(v_fst_3850_, 0);
lean_inc(v_val_3870_);
lean_dec_ref(v_fst_3850_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v_val_3870_);
v___x_3872_ = v___x_3848_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_val_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v___x_3842_);
lean_dec(v_stx_2294_);
v_a_3877_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3845_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3845_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v___x_3885_; uint8_t v___x_3886_; 
v___x_3885_ = l_Lean_Syntax_getArg(v___x_3836_, v___x_3785_);
lean_dec(v___x_3836_);
lean_inc(v___x_3885_);
v___x_3886_ = l_Lean_Syntax_matchesNull(v___x_3885_, v___x_3835_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; lean_object* v_env_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec(v___x_3885_);
v___x_3887_ = lean_st_ref_get(v_a_2300_);
v_env_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc_ref(v_env_3888_);
lean_dec(v___x_3887_);
v___x_3889_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3890_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3891_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3889_, v_env_3888_, v___x_3890_);
v___x_3892_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3893_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3891_, v___x_3892_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3924_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3924_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3924_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v_fst_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3922_; 
v_fst_3898_ = lean_ctor_get(v_a_3894_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_a_3894_);
if (v_isSharedCheck_3922_ == 0)
{
lean_object* v_unused_3923_; 
v_unused_3923_ = lean_ctor_get(v_a_3894_, 1);
lean_dec(v_unused_3923_);
v___x_3900_ = v_a_3894_;
v_isShared_3901_ = v_isSharedCheck_3922_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_fst_3898_);
lean_dec(v_a_3894_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3922_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
if (lean_obj_tag(v_fst_3898_) == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
lean_del_object(v___x_3896_);
v___x_3902_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3903_ = l_Lean_MessageData_ofName(v___x_3890_);
lean_inc_ref(v___x_3903_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set_tag(v___x_3900_, 7);
lean_ctor_set(v___x_3900_, 1, v___x_3903_);
lean_ctor_set(v___x_3900_, 0, v___x_3902_);
v___x_3905_ = v___x_3900_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3906_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3909_ = l_Lean_indentD(v___x_3908_);
v___x_3910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3907_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3910_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v___x_3903_);
v___x_3914_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
lean_inc_ref(v_a_2295_);
v___x_3916_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3915_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3916_;
}
}
else
{
lean_object* v_val_3918_; lean_object* v___x_3920_; 
lean_del_object(v___x_3900_);
lean_dec(v___x_3890_);
lean_dec(v_stx_2294_);
v_val_3918_ = lean_ctor_get(v_fst_3898_, 0);
lean_inc(v_val_3918_);
lean_dec_ref(v_fst_3898_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v_val_3918_);
v___x_3920_ = v___x_3896_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_val_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v___x_3890_);
lean_dec(v_stx_2294_);
v_a_3925_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3893_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3893_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; 
v___x_3933_ = l_Lean_Syntax_getArg(v___x_3885_, v___x_3785_);
lean_dec(v___x_3885_);
v___x_3934_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75));
v___x_3935_ = l_Lean_Syntax_isOfKind(v___x_3933_, v___x_3934_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; lean_object* v_env_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3936_ = lean_st_ref_get(v_a_2300_);
v_env_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc_ref(v_env_3937_);
lean_dec(v___x_3936_);
v___x_3938_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3939_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3940_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3938_, v_env_3937_, v___x_3939_);
v___x_3941_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3942_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3940_, v___x_3941_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3973_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3973_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3973_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v_fst_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3971_; 
v_fst_3947_ = lean_ctor_get(v_a_3943_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v_a_3943_);
if (v_isSharedCheck_3971_ == 0)
{
lean_object* v_unused_3972_; 
v_unused_3972_ = lean_ctor_get(v_a_3943_, 1);
lean_dec(v_unused_3972_);
v___x_3949_ = v_a_3943_;
v_isShared_3950_ = v_isSharedCheck_3971_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_fst_3947_);
lean_dec(v_a_3943_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3971_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
if (lean_obj_tag(v_fst_3947_) == 0)
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3954_; 
lean_del_object(v___x_3945_);
v___x_3951_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3952_ = l_Lean_MessageData_ofName(v___x_3939_);
lean_inc_ref(v___x_3952_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 7);
lean_ctor_set(v___x_3949_, 1, v___x_3952_);
lean_ctor_set(v___x_3949_, 0, v___x_3951_);
v___x_3954_ = v___x_3949_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3955_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_3958_ = l_Lean_indentD(v___x_3957_);
v___x_3959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3956_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3952_);
v___x_3963_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
lean_inc_ref(v_a_2295_);
v___x_3965_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3964_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_3965_;
}
}
else
{
lean_object* v_val_3967_; lean_object* v___x_3969_; 
lean_del_object(v___x_3949_);
lean_dec(v___x_3939_);
lean_dec(v_stx_2294_);
v_val_3967_ = lean_ctor_get(v_fst_3947_, 0);
lean_inc(v_val_3967_);
lean_dec_ref(v_fst_3947_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v_val_3967_);
v___x_3969_ = v___x_3945_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_val_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v___x_3939_);
lean_dec(v_stx_2294_);
v_a_3974_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3942_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3942_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_dec(v_stx_2294_);
v___x_3982_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
return v___x_3983_;
}
}
}
}
}
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v___x_3984_ = lean_unsigned_to_nat(1u);
v___x_3985_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_3984_);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_3987_ = l_Lean_Syntax_isOfKind(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v_env_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3988_ = lean_st_ref_get(v_a_2300_);
v_env_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_ref(v_env_3989_);
lean_dec(v___x_3988_);
v___x_3990_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_3991_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_3992_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3990_, v_env_3989_, v___x_3991_);
v___x_3993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_3994_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_3992_, v___x_3993_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4025_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4025_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4025_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_fst_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4023_; 
v_fst_3999_ = lean_ctor_get(v_a_3995_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_a_3995_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v_a_3995_, 1);
lean_dec(v_unused_4024_);
v___x_4001_ = v_a_3995_;
v_isShared_4002_ = v_isSharedCheck_4023_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_fst_3999_);
lean_dec(v_a_3995_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4023_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
if (lean_obj_tag(v_fst_3999_) == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
lean_del_object(v___x_3997_);
v___x_4003_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4004_ = l_Lean_MessageData_ofName(v___x_3991_);
lean_inc_ref(v___x_4004_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 7);
lean_ctor_set(v___x_4001_, 1, v___x_4004_);
lean_ctor_set(v___x_4001_, 0, v___x_4003_);
v___x_4006_ = v___x_4001_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4006_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
v___x_4009_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_4010_ = l_Lean_indentD(v___x_4009_);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4008_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
lean_ctor_set(v___x_4014_, 1, v___x_4004_);
v___x_4015_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4014_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
lean_inc_ref(v_a_2295_);
v___x_4017_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4016_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_4017_;
}
}
else
{
lean_object* v_val_4019_; lean_object* v___x_4021_; 
lean_del_object(v___x_4001_);
lean_dec(v___x_3991_);
lean_dec(v_stx_2294_);
v_val_4019_ = lean_ctor_get(v_fst_3999_, 0);
lean_inc(v_val_4019_);
lean_dec_ref(v_fst_3999_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v_val_4019_);
v___x_4021_ = v___x_3997_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_val_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec(v___x_3991_);
lean_dec(v_stx_2294_);
v_a_4026_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_3994_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_3994_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_dec(v_stx_2294_);
v___x_4034_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
}
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4036_ = lean_unsigned_to_nat(1u);
v___x_4037_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_4036_);
v___x_4038_ = l_Lean_Syntax_isNone(v___x_4037_);
if (v___x_4038_ == 0)
{
uint8_t v___x_4039_; 
v___x_4039_ = l_Lean_Syntax_matchesNull(v___x_4037_, v___x_4036_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v_env_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_del_object(v___x_2352_);
v___x_4040_ = lean_st_ref_get(v_a_2300_);
v_env_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc_ref(v_env_4041_);
lean_dec(v___x_4040_);
v___x_4042_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_4043_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_4044_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4042_, v_env_4041_, v___x_4043_);
v___x_4045_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_4046_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_4044_, v___x_4045_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4077_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4077_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4077_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_fst_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4075_; 
v_fst_4051_ = lean_ctor_get(v_a_4047_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_a_4047_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v_a_4047_, 1);
lean_dec(v_unused_4076_);
v___x_4053_ = v_a_4047_;
v_isShared_4054_ = v_isSharedCheck_4075_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_fst_4051_);
lean_dec(v_a_4047_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4075_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
if (lean_obj_tag(v_fst_4051_) == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
lean_del_object(v___x_4049_);
v___x_4055_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4056_ = l_Lean_MessageData_ofName(v___x_4043_);
lean_inc_ref(v___x_4056_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set_tag(v___x_4053_, 7);
lean_ctor_set(v___x_4053_, 1, v___x_4056_);
lean_ctor_set(v___x_4053_, 0, v___x_4055_);
v___x_4058_ = v___x_4053_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4059_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4058_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_4062_ = l_Lean_indentD(v___x_4061_);
v___x_4063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4060_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4063_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
lean_ctor_set(v___x_4066_, 1, v___x_4056_);
v___x_4067_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4066_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
lean_inc_ref(v_a_2295_);
v___x_4069_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4068_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_4069_;
}
}
else
{
lean_object* v_val_4071_; lean_object* v___x_4073_; 
lean_del_object(v___x_4053_);
lean_dec(v___x_4043_);
lean_dec(v_stx_2294_);
v_val_4071_ = lean_ctor_get(v_fst_4051_, 0);
lean_inc(v_val_4071_);
lean_dec_ref(v_fst_4051_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_val_4071_);
v___x_4073_ = v___x_4049_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_val_4071_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec(v___x_4043_);
lean_dec(v_stx_2294_);
v_a_4078_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4046_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4046_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
else
{
v___y_2369_ = v_a_2295_;
v___y_2370_ = v_a_2296_;
v___y_2371_ = v_a_2297_;
v___y_2372_ = v_a_2298_;
v___y_2373_ = v_a_2299_;
v___y_2374_ = v_a_2300_;
goto v___jp_2368_;
}
}
else
{
lean_dec(v___x_4037_);
v___y_2369_ = v_a_2295_;
v___y_2370_ = v_a_2296_;
v___y_2371_ = v_a_2297_;
v___y_2372_ = v_a_2298_;
v___y_2373_ = v_a_2299_;
v___y_2374_ = v_a_2300_;
goto v___jp_2368_;
}
}
}
else
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_del_object(v___x_2352_);
v___x_4086_ = lean_unsigned_to_nat(1u);
v___x_4087_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_4086_);
lean_dec(v_stx_2294_);
v___x_4088_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4087_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_4088_;
}
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_del_object(v___x_2352_);
lean_dec(v_stx_2294_);
v___x_4089_ = lean_unsigned_to_nat(1u);
v___x_4090_ = l_Lean_NameSet_empty;
v___x_4091_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*2, v___x_2435_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*2 + 1, v___x_2435_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*2 + 2, v___x_2435_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
else
{
lean_object* v___x_4093_; lean_object* v___x_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
lean_del_object(v___x_2352_);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4098_ = lean_unsigned_to_nat(1u);
v___x_4099_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_4098_);
v___x_4100_ = l_Lean_Syntax_isNone(v___x_4099_);
if (v___x_4100_ == 0)
{
uint8_t v___x_4101_; 
v___x_4101_ = l_Lean_Syntax_matchesNull(v___x_4099_, v___x_4098_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; lean_object* v_env_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4102_ = lean_st_ref_get(v_a_2300_);
v_env_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc_ref(v_env_4103_);
lean_dec(v___x_4102_);
v___x_4104_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_4105_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_4106_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4104_, v_env_4103_, v___x_4105_);
v___x_4107_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_4108_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_4106_, v___x_4107_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4139_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4139_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4139_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v_fst_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4137_; 
v_fst_4113_ = lean_ctor_get(v_a_4109_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_a_4109_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v_a_4109_, 1);
lean_dec(v_unused_4138_);
v___x_4115_ = v_a_4109_;
v_isShared_4116_ = v_isSharedCheck_4137_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_fst_4113_);
lean_dec(v_a_4109_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4137_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
if (lean_obj_tag(v_fst_4113_) == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
lean_del_object(v___x_4111_);
v___x_4117_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4118_ = l_Lean_MessageData_ofName(v___x_4105_);
lean_inc_ref(v___x_4118_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set_tag(v___x_4115_, 7);
lean_ctor_set(v___x_4115_, 1, v___x_4118_);
lean_ctor_set(v___x_4115_, 0, v___x_4117_);
v___x_4120_ = v___x_4115_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4117_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4121_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_4124_ = l_Lean_indentD(v___x_4123_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4122_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v___x_4118_);
v___x_4129_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
lean_inc_ref(v_a_2295_);
v___x_4131_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4130_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_4131_;
}
}
else
{
lean_object* v_val_4133_; lean_object* v___x_4135_; 
lean_del_object(v___x_4115_);
lean_dec(v___x_4105_);
lean_dec(v_stx_2294_);
v_val_4133_ = lean_ctor_get(v_fst_4113_, 0);
lean_inc(v_val_4133_);
lean_dec_ref(v_fst_4113_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v_val_4133_);
v___x_4135_ = v___x_4111_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_val_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v___x_4105_);
lean_dec(v_stx_2294_);
v_a_4140_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4108_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4108_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_dec(v_stx_2294_);
goto v___jp_4094_;
}
}
else
{
lean_dec(v___x_4099_);
lean_dec(v_stx_2294_);
goto v___jp_4094_;
}
v___jp_4094_:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4095_ = l_Lean_NameSet_empty;
v___x_4096_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4096_, 0, v___x_4093_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*2, v___x_2433_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*2 + 1, v___x_2433_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*2 + 2, v___x_2431_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
return v___x_4097_;
}
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_del_object(v___x_2352_);
lean_dec(v_stx_2294_);
v___x_4148_ = lean_unsigned_to_nat(0u);
v___x_4149_ = l_Lean_NameSet_empty;
v___x_4150_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
lean_ctor_set_uint8(v___x_4150_, sizeof(void*)*2, v___x_2430_);
lean_ctor_set_uint8(v___x_4150_, sizeof(void*)*2 + 1, v___x_2431_);
lean_ctor_set_uint8(v___x_4150_, sizeof(void*)*2 + 2, v___x_2430_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_del_object(v___x_2352_);
lean_dec(v_stx_2294_);
v___x_4152_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
return v___x_4153_;
}
v___jp_2368_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2375_ = lean_unsigned_to_nat(2u);
v___x_2376_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2378_ = l_Lean_Syntax_isOfKind(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v_env_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_del_object(v___x_2352_);
v___x_2379_ = lean_st_ref_get(v___y_2374_);
v_env_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc_ref(v_env_2380_);
lean_dec(v___x_2379_);
v___x_2381_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(v_stx_2294_);
v___x_2382_ = l_Lean_Syntax_getKind(v_stx_2294_);
v___x_2383_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2381_, v_env_2380_, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(v_stx_2294_);
v___x_2385_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2294_, v___x_2383_, v___x_2384_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2416_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2416_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2416_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_fst_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2414_; 
v_fst_2390_ = lean_ctor_get(v_a_2386_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_a_2386_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v_a_2386_, 1);
lean_dec(v_unused_2415_);
v___x_2392_ = v_a_2386_;
v_isShared_2393_ = v_isSharedCheck_2414_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_fst_2390_);
lean_dec(v_a_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2414_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
if (lean_obj_tag(v_fst_2390_) == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_del_object(v___x_2388_);
v___x_2394_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2395_ = l_Lean_MessageData_ofName(v___x_2382_);
lean_inc_ref(v___x_2395_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 7);
lean_ctor_set(v___x_2392_, 1, v___x_2395_);
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2397_ = v___x_2392_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2398_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_MessageData_ofSyntax(v_stx_2294_);
v___x_2401_ = l_Lean_indentD(v___x_2400_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2399_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2395_);
v___x_2406_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
lean_inc_ref(v___y_2369_);
v___x_2408_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2407_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
return v___x_2408_;
}
}
else
{
lean_object* v_val_2410_; lean_object* v___x_2412_; 
lean_del_object(v___x_2392_);
lean_dec(v___x_2382_);
lean_dec(v_stx_2294_);
v_val_2410_ = lean_ctor_get(v_fst_2390_, 0);
lean_inc(v_val_2410_);
lean_dec_ref(v_fst_2390_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v_val_2410_);
v___x_2412_ = v___x_2388_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_val_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v___x_2382_);
lean_dec(v_stx_2294_);
v_a_2417_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2385_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2385_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec(v_stx_2294_);
v___x_2425_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2425_);
v___x_2427_ = v___x_2352_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec(v_stx_2294_);
v_a_4155_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_2349_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_2349_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
v___jp_2302_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2311_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___y_2309_);
v___x_2314_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2311_, v___x_2312_, v___x_2313_, v___y_2310_, v___y_2304_, v___y_2303_, v___y_2307_, v___y_2306_, v___y_2305_, v___y_2308_);
return v___x_2314_;
}
v___jp_2315_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2322_ = lean_unsigned_to_nat(6u);
v___x_2323_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2322_);
v___x_2324_ = lean_unsigned_to_nat(7u);
v___x_2325_ = l_Lean_Syntax_getArg(v_stx_2294_, v___x_2324_);
lean_dec(v_stx_2294_);
v___x_2326_ = l_Lean_Syntax_getOptional_x3f(v___x_2325_);
lean_dec(v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_box(0);
v___y_2303_ = v___y_2317_;
v___y_2304_ = v___y_2316_;
v___y_2305_ = v___y_2320_;
v___y_2306_ = v___y_2319_;
v___y_2307_ = v___y_2318_;
v___y_2308_ = v___y_2321_;
v___y_2309_ = v___x_2323_;
v___y_2310_ = v___x_2327_;
goto v___jp_2302_;
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_val_2328_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2326_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_val_2328_);
lean_dec(v___x_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_val_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v___y_2303_ = v___y_2317_;
v___y_2304_ = v___y_2316_;
v___y_2305_ = v___y_2320_;
v___y_2306_ = v___y_2319_;
v___y_2307_ = v___y_2318_;
v___y_2308_ = v___y_2321_;
v___y_2309_ = v___x_2323_;
v___y_2310_ = v___x_2333_;
goto v___jp_2302_;
}
}
}
}
v___jp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2337_, v_bodyInfo_2338_);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
return v___x_2340_;
}
v___jp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2342_, v_bodyInfo_2343_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4163_, size_t v_sz_4164_, size_t v_i_4165_, lean_object* v_b_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
uint8_t v___x_4174_; 
v___x_4174_ = lean_usize_dec_lt(v_i_4165_, v_sz_4164_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v_b_4166_);
return v___x_4175_;
}
else
{
uint8_t v_breaks_4176_; uint8_t v_continues_4177_; uint8_t v_returnsEarly_4178_; lean_object* v_numRegularExits_4179_; lean_object* v_reassigns_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v_breaks_4176_ = lean_ctor_get_uint8(v_b_4166_, sizeof(void*)*2);
v_continues_4177_ = lean_ctor_get_uint8(v_b_4166_, sizeof(void*)*2 + 1);
v_returnsEarly_4178_ = lean_ctor_get_uint8(v_b_4166_, sizeof(void*)*2 + 2);
v_numRegularExits_4179_ = lean_ctor_get(v_b_4166_, 0);
v_reassigns_4180_ = lean_ctor_get(v_b_4166_, 1);
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = lean_nat_dec_eq(v_numRegularExits_4179_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4184_; 
lean_inc(v_reassigns_4180_);
lean_dec_ref(v_b_4166_);
v_a_4183_ = lean_array_uget_borrowed(v_as_4163_, v_i_4165_);
lean_inc(v_a_4183_);
v___x_4184_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4183_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; uint8_t v___y_4187_; uint8_t v___y_4188_; uint8_t v___y_4189_; uint8_t v___y_4204_; uint8_t v___y_4205_; uint8_t v___y_4208_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref(v___x_4184_);
if (v_breaks_4176_ == 0)
{
uint8_t v_breaks_4210_; 
v_breaks_4210_ = lean_ctor_get_uint8(v_a_4185_, sizeof(void*)*2);
v___y_4208_ = v_breaks_4210_;
goto v___jp_4207_;
}
else
{
v___y_4208_ = v___x_4174_;
goto v___jp_4207_;
}
v___jp_4186_:
{
lean_object* v_numRegularExits_4190_; lean_object* v_reassigns_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4202_; 
v_numRegularExits_4190_ = lean_ctor_get(v_a_4185_, 0);
v_reassigns_4191_ = lean_ctor_get(v_a_4185_, 1);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_a_4185_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4193_ = v_a_4185_;
v_isShared_4194_ = v_isSharedCheck_4202_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_reassigns_4191_);
lean_inc(v_numRegularExits_4190_);
lean_dec(v_a_4185_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4202_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4195_ = l_Lean_NameSet_append(v_reassigns_4180_, v_reassigns_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___x_4195_);
v___x_4197_ = v___x_4193_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_numRegularExits_4190_);
lean_ctor_set(v_reuseFailAlloc_4201_, 1, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
size_t v___x_4198_; size_t v___x_4199_; 
lean_ctor_set_uint8(v___x_4197_, sizeof(void*)*2, v___y_4187_);
lean_ctor_set_uint8(v___x_4197_, sizeof(void*)*2 + 1, v___y_4188_);
lean_ctor_set_uint8(v___x_4197_, sizeof(void*)*2 + 2, v___y_4189_);
v___x_4198_ = ((size_t)1ULL);
v___x_4199_ = lean_usize_add(v_i_4165_, v___x_4198_);
v_i_4165_ = v___x_4199_;
v_b_4166_ = v___x_4197_;
goto _start;
}
}
}
v___jp_4203_:
{
if (v_returnsEarly_4178_ == 0)
{
uint8_t v_returnsEarly_4206_; 
v_returnsEarly_4206_ = lean_ctor_get_uint8(v_a_4185_, sizeof(void*)*2 + 2);
v___y_4187_ = v___y_4204_;
v___y_4188_ = v___y_4205_;
v___y_4189_ = v_returnsEarly_4206_;
goto v___jp_4186_;
}
else
{
v___y_4187_ = v___y_4204_;
v___y_4188_ = v___y_4205_;
v___y_4189_ = v___x_4174_;
goto v___jp_4186_;
}
}
v___jp_4207_:
{
if (v_continues_4177_ == 0)
{
uint8_t v_continues_4209_; 
v_continues_4209_ = lean_ctor_get_uint8(v_a_4185_, sizeof(void*)*2 + 1);
v___y_4204_ = v___y_4208_;
v___y_4205_ = v_continues_4209_;
goto v___jp_4203_;
}
else
{
v___y_4204_ = v___y_4208_;
v___y_4205_ = v___x_4174_;
goto v___jp_4203_;
}
}
}
else
{
lean_dec(v_reassigns_4180_);
return v___x_4184_;
}
}
else
{
lean_object* v___x_4211_; 
v___x_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4211_, 0, v_b_4166_);
return v___x_4211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_info_4220_; lean_object* v___x_4221_; size_t v_sz_4222_; size_t v___x_4223_; lean_object* v___x_4224_; 
v_info_4220_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___x_4221_ = l_Lean_Parser_Term_getDoElems(v_stx_4212_);
v_sz_4222_ = lean_array_size(v___x_4221_);
v___x_4223_ = ((size_t)0ULL);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4221_, v_sz_4222_, v___x_4223_, v_info_4220_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_);
lean_dec_ref(v___x_4221_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_b_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
size_t v_sz_boxed_4254_; size_t v_i_boxed_4255_; lean_object* v_res_4256_; 
v_sz_boxed_4254_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4255_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4243_, v_sz_boxed_4254_, v_i_boxed_4255_, v_b_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec_ref(v_as_4243_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4257_, lean_object* v_sz_4258_, lean_object* v_i_4259_, lean_object* v_b_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
size_t v_sz_boxed_4268_; size_t v_i_boxed_4269_; lean_object* v_res_4270_; 
v_sz_boxed_4268_ = lean_unbox_usize(v_sz_4258_);
lean_dec(v_sz_4258_);
v_i_boxed_4269_ = lean_unbox_usize(v_i_4259_);
lean_dec(v_i_4259_);
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4257_, v_sz_boxed_4268_, v_i_boxed_4269_, v_b_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v_as_4257_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4271_, lean_object* v_rhs_x3f_4272_, lean_object* v_otherwise_x3f_4273_, lean_object* v_body_x3f_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4271_, v_rhs_x3f_4272_, v_otherwise_x3f_4273_, v_body_x3f_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4283_, lean_object* v_as_4284_, lean_object* v_sz_4285_, lean_object* v_i_4286_, lean_object* v_b_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
uint8_t v___x_261289__boxed_4295_; size_t v_sz_boxed_4296_; size_t v_i_boxed_4297_; lean_object* v_res_4298_; 
v___x_261289__boxed_4295_ = lean_unbox(v___x_4283_);
v_sz_boxed_4296_ = lean_unbox_usize(v_sz_4285_);
lean_dec(v_sz_4285_);
v_i_boxed_4297_ = lean_unbox_usize(v_i_4286_);
lean_dec(v_i_4286_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_261289__boxed_4295_, v_as_4284_, v_sz_boxed_4296_, v_i_boxed_4297_, v_b_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_as_4284_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4299_, lean_object* v_as_4300_, lean_object* v_sz_4301_, lean_object* v_i_4302_, lean_object* v_b_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
uint8_t v___x_261340__boxed_4311_; size_t v_sz_boxed_4312_; size_t v_i_boxed_4313_; lean_object* v_res_4314_; 
v___x_261340__boxed_4311_ = lean_unbox(v___x_4299_);
v_sz_boxed_4312_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v_i_boxed_4313_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_res_4314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_261340__boxed_4311_, v_as_4300_, v_sz_boxed_4312_, v_i_boxed_4313_, v_b_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_as_4300_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4315_, lean_object* v_sz_4316_, lean_object* v_i_4317_, lean_object* v_b_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
size_t v_sz_boxed_4326_; size_t v_i_boxed_4327_; lean_object* v_res_4328_; 
v_sz_boxed_4326_ = lean_unbox_usize(v_sz_4316_);
lean_dec(v_sz_4316_);
v_i_boxed_4327_ = lean_unbox_usize(v_i_4317_);
lean_dec(v_i_4317_);
v_res_4328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4315_, v_sz_boxed_4326_, v_i_boxed_4327_, v_b_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec_ref(v_as_4315_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4329_, lean_object* v_decl_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
uint8_t v_reassignment_boxed_4338_; lean_object* v_res_4339_; 
v_reassignment_boxed_4338_ = lean_unbox(v_reassignment_4329_);
v_res_4339_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4338_, v_decl_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4367_, v___y_4372_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7(lean_object* v_00_u03b1_4385_, lean_object* v_ref_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(v_ref_4386_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___boxed(lean_object* v_00_u03b1_4395_, lean_object* v_ref_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7(v_00_u03b1_4395_, v_ref_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4405_, lean_object* v_x_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___x_4414_; 
lean_inc_ref(v___y_4411_);
v___x_4414_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4415_, lean_object* v_x_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4415_, v_x_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4425_, lean_object* v_as_4426_, lean_object* v_as_x27_4427_, lean_object* v_b_4428_, lean_object* v_a_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4425_, v_as_x27_4427_, v_b_4428_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4438_, lean_object* v_as_4439_, lean_object* v_as_x27_4440_, lean_object* v_b_4441_, lean_object* v_a_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4438_, v_as_4439_, v_as_x27_4440_, v_b_4441_, v_a_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v_as_4439_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4451_, lean_object* v_msg_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
lean_inc_ref(v___y_4453_);
v___x_4460_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4461_, lean_object* v_msg_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4461_, v_msg_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_cls_4471_, lean_object* v_msg_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(v_cls_4471_, v_msg_4472_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_cls_4481_, lean_object* v_msg_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_cls_4481_, v_msg_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_4491_, lean_object* v_as_x27_4492_, lean_object* v_b_4493_, lean_object* v_a_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(v_as_x27_4492_, v_b_4493_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_4503_, lean_object* v_as_x27_4504_, lean_object* v_b_4505_, lean_object* v_a_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_4503_, v_as_x27_4504_, v_b_4505_, v_a_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v_as_4503_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4515_, lean_object* v_ref_4516_, lean_object* v_msg_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4516_, v_msg_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4526_, lean_object* v_ref_4527_, lean_object* v_msg_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4526_, v_ref_4527_, v_msg_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v_ref_4527_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12(lean_object* v_msgData_4537_, lean_object* v_macroStack_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(v_msgData_4537_, v_macroStack_4538_, v___y_4543_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___boxed(lean_object* v_msgData_4547_, lean_object* v_macroStack_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12(v_msgData_4547_, v_macroStack_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11(lean_object* v_00_u03b2_4557_, lean_object* v_m_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v___x_4560_; 
v___x_4560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(v_m_4558_, v_a_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b2_4561_, lean_object* v_m_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11(v_00_u03b2_4561_, v_m_4562_, v_a_4563_);
lean_dec(v_a_4563_);
lean_dec_ref(v_m_4562_);
return v_res_4564_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27(lean_object* v_00_u03b2_4565_, lean_object* v_x_4566_, lean_object* v_x_4567_){
_start:
{
uint8_t v___x_4568_; 
v___x_4568_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(v_x_4566_, v_x_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___boxed(lean_object* v_00_u03b2_4569_, lean_object* v_x_4570_, lean_object* v_x_4571_){
_start:
{
uint8_t v_res_4572_; lean_object* v_r_4573_; 
v_res_4572_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27(v_00_u03b2_4569_, v_x_4570_, v_x_4571_);
lean_dec_ref(v_x_4571_);
v_r_4573_ = lean_box(v_res_4572_);
return v_r_4573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30(lean_object* v_00_u03b2_4574_, lean_object* v_a_4575_, lean_object* v_x_4576_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(v_a_4575_, v_x_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___boxed(lean_object* v_00_u03b2_4578_, lean_object* v_a_4579_, lean_object* v_x_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30(v_00_u03b2_4578_, v_a_4579_, v_x_4580_);
lean_dec(v_x_4580_);
lean_dec(v_a_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33(lean_object* v_00_u03b2_4582_, lean_object* v_x_4583_, size_t v_x_4584_, lean_object* v_x_4585_){
_start:
{
uint8_t v___x_4586_; 
v___x_4586_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(v_x_4583_, v_x_4584_, v_x_4585_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___boxed(lean_object* v_00_u03b2_4587_, lean_object* v_x_4588_, lean_object* v_x_4589_, lean_object* v_x_4590_){
_start:
{
size_t v_x_266624__boxed_4591_; uint8_t v_res_4592_; lean_object* v_r_4593_; 
v_x_266624__boxed_4591_ = lean_unbox_usize(v_x_4589_);
lean_dec(v_x_4589_);
v_res_4592_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33(v_00_u03b2_4587_, v_x_4588_, v_x_266624__boxed_4591_, v_x_4590_);
lean_dec_ref(v_x_4590_);
v_r_4593_ = lean_box(v_res_4592_);
return v_r_4593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37(lean_object* v_00_u03b2_4594_, lean_object* v_keys_4595_, lean_object* v_vals_4596_, lean_object* v_heq_4597_, lean_object* v_i_4598_, lean_object* v_k_4599_){
_start:
{
uint8_t v___x_4600_; 
v___x_4600_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(v_keys_4595_, v_i_4598_, v_k_4599_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___boxed(lean_object* v_00_u03b2_4601_, lean_object* v_keys_4602_, lean_object* v_vals_4603_, lean_object* v_heq_4604_, lean_object* v_i_4605_, lean_object* v_k_4606_){
_start:
{
uint8_t v_res_4607_; lean_object* v_r_4608_; 
v_res_4607_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37(v_00_u03b2_4601_, v_keys_4602_, v_vals_4603_, v_heq_4604_, v_i_4605_, v_k_4606_);
lean_dec_ref(v_k_4606_);
lean_dec_ref(v_vals_4603_);
lean_dec_ref(v_keys_4602_);
v_r_4608_ = lean_box(v_res_4607_);
return v_r_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
return v_res_4644_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Do_instInhabitedControlInfo_default = _init_l_Lean_Elab_Do_instInhabitedControlInfo_default();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo_default);
l_Lean_Elab_Do_instInhabitedControlInfo = _init_l_Lean_Elab_Do_instInhabitedControlInfo();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo);
l_Lean_Elab_Do_ControlInfo_pure = _init_l_Lean_Elab_Do_ControlInfo_pure();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_pure);
res = l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
res = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_InferControlInfo(builtin);
}
#ifdef __cplusplus
}
#endif
