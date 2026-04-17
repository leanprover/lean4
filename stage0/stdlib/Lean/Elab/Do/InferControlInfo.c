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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
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
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 249, .m_capacity = 249, .m_length = 246, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `TSyntax \\`doElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78;
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; 
v___x_1_ = l_Lean_NameSet_empty;
v___x_2_ = lean_unsigned_to_nat(1u);
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
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_breaks_10_; uint8_t v_continues_11_; uint8_t v_returnsEarly_12_; lean_object* v_numRegularExits_13_; lean_object* v_reassigns_14_; uint8_t v___y_16_; uint8_t v___y_17_; uint8_t v___y_18_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_breaks_10_ = lean_ctor_get_uint8(v_a_8_, sizeof(void*)*2);
v_continues_11_ = lean_ctor_get_uint8(v_a_8_, sizeof(void*)*2 + 1);
v_returnsEarly_12_ = lean_ctor_get_uint8(v_a_8_, sizeof(void*)*2 + 2);
v_numRegularExits_13_ = lean_ctor_get(v_a_8_, 0);
v_reassigns_14_ = lean_ctor_get(v_a_8_, 1);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_nat_dec_eq(v_numRegularExits_13_, v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; uint8_t v___y_33_; uint8_t v___y_34_; uint8_t v___y_37_; 
lean_inc(v_reassigns_14_);
lean_dec_ref(v_a_8_);
v___x_31_ = 1;
if (v_breaks_10_ == 0)
{
uint8_t v_breaks_39_; 
v_breaks_39_ = lean_ctor_get_uint8(v_b_9_, sizeof(void*)*2);
v___y_37_ = v_breaks_39_;
goto v___jp_36_;
}
else
{
v___y_37_ = v___x_31_;
goto v___jp_36_;
}
v___jp_32_:
{
if (v_returnsEarly_12_ == 0)
{
uint8_t v_returnsEarly_35_; 
v_returnsEarly_35_ = lean_ctor_get_uint8(v_b_9_, sizeof(void*)*2 + 2);
v___y_16_ = v___y_34_;
v___y_17_ = v___y_33_;
v___y_18_ = v_returnsEarly_35_;
goto v___jp_15_;
}
else
{
v___y_16_ = v___y_34_;
v___y_17_ = v___y_33_;
v___y_18_ = v___x_31_;
goto v___jp_15_;
}
}
v___jp_36_:
{
if (v_continues_11_ == 0)
{
uint8_t v_continues_38_; 
v_continues_38_ = lean_ctor_get_uint8(v_b_9_, sizeof(void*)*2 + 1);
v___y_33_ = v___y_37_;
v___y_34_ = v_continues_38_;
goto v___jp_32_;
}
else
{
v___y_33_ = v___y_37_;
v___y_34_ = v___x_31_;
goto v___jp_32_;
}
}
}
else
{
lean_dec_ref(v_b_9_);
return v_a_8_;
}
v___jp_15_:
{
lean_object* v_numRegularExits_19_; lean_object* v_reassigns_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_numRegularExits_19_ = lean_ctor_get(v_b_9_, 0);
v_reassigns_20_ = lean_ctor_get(v_b_9_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_b_9_);
if (v_isSharedCheck_28_ == 0)
{
v___x_22_ = v_b_9_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_reassigns_20_);
lean_inc(v_numRegularExits_19_);
lean_dec(v_b_9_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = l_Lean_NameSet_append(v_reassigns_14_, v_reassigns_20_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_24_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_numRegularExits_19_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*2, v___y_17_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*2 + 1, v___y_16_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*2 + 2, v___y_18_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
uint8_t v_breaks_42_; uint8_t v_continues_43_; uint8_t v_returnsEarly_44_; lean_object* v_numRegularExits_45_; lean_object* v_reassigns_46_; uint8_t v___y_48_; uint8_t v___y_49_; uint8_t v___y_50_; uint8_t v___y_63_; uint8_t v___y_64_; uint8_t v___y_67_; 
v_breaks_42_ = lean_ctor_get_uint8(v_a_40_, sizeof(void*)*2);
v_continues_43_ = lean_ctor_get_uint8(v_a_40_, sizeof(void*)*2 + 1);
v_returnsEarly_44_ = lean_ctor_get_uint8(v_a_40_, sizeof(void*)*2 + 2);
v_numRegularExits_45_ = lean_ctor_get(v_a_40_, 0);
lean_inc(v_numRegularExits_45_);
v_reassigns_46_ = lean_ctor_get(v_a_40_, 1);
lean_inc(v_reassigns_46_);
lean_dec_ref(v_a_40_);
if (v_breaks_42_ == 0)
{
uint8_t v_breaks_69_; 
v_breaks_69_ = lean_ctor_get_uint8(v_b_41_, sizeof(void*)*2);
v___y_67_ = v_breaks_69_;
goto v___jp_66_;
}
else
{
v___y_67_ = v_breaks_42_;
goto v___jp_66_;
}
v___jp_47_:
{
lean_object* v_numRegularExits_51_; lean_object* v_reassigns_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_61_; 
v_numRegularExits_51_ = lean_ctor_get(v_b_41_, 0);
v_reassigns_52_ = lean_ctor_get(v_b_41_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_b_41_);
if (v_isSharedCheck_61_ == 0)
{
v___x_54_ = v_b_41_;
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_reassigns_52_);
lean_inc(v_numRegularExits_51_);
lean_dec(v_b_41_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_56_ = lean_nat_add(v_numRegularExits_45_, v_numRegularExits_51_);
lean_dec(v_numRegularExits_51_);
lean_dec(v_numRegularExits_45_);
v___x_57_ = l_Lean_NameSet_append(v_reassigns_46_, v_reassigns_52_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 1, v___x_57_);
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_59_ = v___x_54_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*2, v___y_49_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*2 + 1, v___y_48_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*2 + 2, v___y_50_);
return v___x_59_;
}
}
}
v___jp_62_:
{
if (v_returnsEarly_44_ == 0)
{
uint8_t v_returnsEarly_65_; 
v_returnsEarly_65_ = lean_ctor_get_uint8(v_b_41_, sizeof(void*)*2 + 2);
v___y_48_ = v___y_64_;
v___y_49_ = v___y_63_;
v___y_50_ = v_returnsEarly_65_;
goto v___jp_47_;
}
else
{
v___y_48_ = v___y_64_;
v___y_49_ = v___y_63_;
v___y_50_ = v_returnsEarly_44_;
goto v___jp_47_;
}
}
v___jp_66_:
{
if (v_continues_43_ == 0)
{
uint8_t v_continues_68_; 
v_continues_68_ = lean_ctor_get_uint8(v_b_41_, sizeof(void*)*2 + 1);
v___y_63_ = v___y_67_;
v___y_64_ = v_continues_68_;
goto v___jp_62_;
}
else
{
v___y_63_ = v___y_67_;
v___y_64_ = v_continues_43_;
goto v___jp_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_70_, lean_object* v_x2_71_, lean_object* v_x3_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v_x1_70_);
lean_ctor_set(v___x_73_, 1, v_x3_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_76_ = l_Lean_stringToMessageData(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2));
v___x_79_ = l_Lean_stringToMessageData(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_107_ = l_Lean_stringToMessageData(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_110_ = l_Lean_stringToMessageData(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_111_, lean_object* v_info_112_){
_start:
{
uint8_t v_breaks_113_; uint8_t v_continues_114_; uint8_t v_returnsEarly_115_; lean_object* v_numRegularExits_116_; lean_object* v_reassigns_117_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___y_140_; lean_object* v___y_141_; lean_object* v___x_149_; lean_object* v___y_151_; 
v_breaks_113_ = lean_ctor_get_uint8(v_info_112_, sizeof(void*)*2);
v_continues_114_ = lean_ctor_get_uint8(v_info_112_, sizeof(void*)*2 + 1);
v_returnsEarly_115_ = lean_ctor_get_uint8(v_info_112_, sizeof(void*)*2 + 2);
v_numRegularExits_116_ = lean_ctor_get(v_info_112_, 0);
lean_inc(v_numRegularExits_116_);
v_reassigns_117_ = lean_ctor_get(v_info_112_, 1);
lean_inc(v_reassigns_117_);
lean_dec_ref(v_info_112_);
v___x_149_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
if (v_breaks_113_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_151_ = v___x_159_;
goto v___jp_150_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_151_ = v___x_160_;
goto v___jp_150_;
}
v___jp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_inc_ref(v___y_120_);
v___x_121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_121_, 0, v___y_120_);
v___x_122_ = l_Lean_MessageData_ofFormat(v___x_121_);
v___x_123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_119_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = l_Nat_reprFast(v_numRegularExits_116_);
v___x_127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
v___x_128_ = l_Lean_MessageData_ofFormat(v___x_127_);
v___x_129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_125_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3);
v___x_131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_box(0);
v___x_133_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_134_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_133_, v___f_111_, v___x_132_, v_reassigns_117_);
v___x_135_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14));
v___x_136_ = l_List_mapTR_loop___redArg(v___x_135_, v___x_134_, v___x_132_);
v___x_137_ = l_Lean_MessageData_ofList(v___x_136_);
v___x_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_131_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
return v___x_138_;
}
v___jp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
lean_inc_ref(v___y_141_);
v___x_142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_142_, 0, v___y_141_);
v___x_143_ = l_Lean_MessageData_ofFormat(v___x_142_);
v___x_144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_140_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
if (v_returnsEarly_115_ == 0)
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_119_ = v___x_146_;
v___y_120_ = v___x_147_;
goto v___jp_118_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_119_ = v___x_146_;
v___y_120_ = v___x_148_;
goto v___jp_118_;
}
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_inc_ref(v___y_151_);
v___x_152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_152_, 0, v___y_151_);
v___x_153_ = l_Lean_MessageData_ofFormat(v___x_152_);
v___x_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_149_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
v___x_156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
if (v_continues_114_ == 0)
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_140_ = v___x_156_;
v___y_141_ = v___x_157_;
goto v___jp_139_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_140_ = v___x_156_;
v___y_141_ = v___x_158_;
goto v___jp_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_189_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_192_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_193_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_194_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_195_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_196_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_191_, v___x_192_, v___x_193_, v___x_194_, v___x_195_, v_ref_189_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_208_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_215_ = l_Lean_addBuiltinDocString(v___x_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_245_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_246_ = l_Lean_addBuiltinDeclarationRanges(v___x_244_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_env_256_; lean_object* v___x_257_; lean_object* v_mctx_258_; lean_object* v_lctx_259_; lean_object* v_options_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_255_ = lean_st_ref_get(v___y_253_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_255_);
v___x_257_ = lean_st_ref_get(v___y_251_);
v_mctx_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_mctx_258_);
lean_dec(v___x_257_);
v_lctx_259_ = lean_ctor_get(v___y_250_, 2);
v_options_260_ = lean_ctor_get(v___y_252_, 2);
lean_inc_ref(v_options_260_);
lean_inc_ref(v_lctx_259_);
v___x_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_261_, 0, v_env_256_);
lean_ctor_set(v___x_261_, 1, v_mctx_258_);
lean_ctor_set(v___x_261_, 2, v_lctx_259_);
lean_ctor_set(v___x_261_, 3, v_options_260_);
v___x_262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_msgData_249_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_box(1);
v___x_272_ = l_Lean_MessageData_ofFormat(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
return v_x_278_;
}
else
{
lean_object* v_head_280_; lean_object* v_tail_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_303_; 
v_head_280_ = lean_ctor_get(v_x_279_, 0);
v_tail_281_ = lean_ctor_get(v_x_279_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_303_ == 0)
{
v___x_283_ = v_x_279_;
v_isShared_284_ = v_isSharedCheck_303_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_tail_281_);
lean_inc(v_head_280_);
lean_dec(v_x_279_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_303_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_before_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_301_; 
v_before_285_ = lean_ctor_get(v_head_280_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_head_280_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_head_280_, 1);
lean_dec(v_unused_302_);
v___x_287_ = v_head_280_;
v_isShared_288_ = v_isSharedCheck_301_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_before_285_);
lean_dec(v_head_280_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_301_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 7);
lean_ctor_set(v___x_287_, 1, v___x_289_);
lean_ctor_set(v___x_287_, 0, v_x_278_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_x_278_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_300_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 7);
lean_ctor_set(v___x_283_, 1, v___x_292_);
lean_ctor_set(v___x_283_, 0, v___x_291_);
v___x_294_ = v___x_283_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_299_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_MessageData_ofSyntax(v_before_285_);
v___x_296_ = l_Lean_indentD(v___x_295_);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_294_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v_x_278_ = v___x_297_;
v_x_279_ = v_tail_281_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_304_, lean_object* v_opt_305_){
_start:
{
lean_object* v_name_306_; lean_object* v_defValue_307_; lean_object* v_map_308_; lean_object* v___x_309_; 
v_name_306_ = lean_ctor_get(v_opt_305_, 0);
v_defValue_307_ = lean_ctor_get(v_opt_305_, 1);
v_map_308_ = lean_ctor_get(v_opts_304_, 0);
v___x_309_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_308_, v_name_306_);
if (lean_obj_tag(v___x_309_) == 0)
{
uint8_t v___x_310_; 
v___x_310_ = lean_unbox(v_defValue_307_);
return v___x_310_;
}
else
{
lean_object* v_val_311_; 
v_val_311_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_val_311_);
lean_dec_ref(v___x_309_);
if (lean_obj_tag(v_val_311_) == 1)
{
uint8_t v_v_312_; 
v_v_312_ = lean_ctor_get_uint8(v_val_311_, 0);
lean_dec_ref(v_val_311_);
return v_v_312_;
}
else
{
uint8_t v___x_313_; 
lean_dec(v_val_311_);
v___x_313_ = lean_unbox(v_defValue_307_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_314_, lean_object* v_opt_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_314_, v_opt_315_);
lean_dec_ref(v_opt_315_);
lean_dec_ref(v_opts_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_323_, lean_object* v_macroStack_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_options_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_options_327_ = lean_ctor_get(v___y_325_, 2);
v___x_328_ = l_Lean_Elab_pp_macroStack;
v___x_329_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec(v_macroStack_324_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_msgData_323_);
return v___x_330_;
}
else
{
if (lean_obj_tag(v_macroStack_324_) == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_msgData_323_);
return v___x_331_;
}
else
{
lean_object* v_head_332_; lean_object* v_after_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_348_; 
v_head_332_ = lean_ctor_get(v_macroStack_324_, 0);
lean_inc(v_head_332_);
v_after_333_ = lean_ctor_get(v_head_332_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_head_332_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_head_332_, 0);
lean_dec(v_unused_349_);
v___x_335_ = v_head_332_;
v_isShared_336_ = v_isSharedCheck_348_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_after_333_);
lean_dec(v_head_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_348_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 7);
lean_ctor_set(v___x_335_, 1, v___x_337_);
lean_ctor_set(v___x_335_, 0, v_msgData_323_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_msgData_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_347_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_msgData_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_340_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = l_Lean_MessageData_ofSyntax(v_after_333_);
v___x_343_ = l_Lean_indentD(v___x_342_);
v_msgData_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_344_, 0, v___x_341_);
lean_ctor_set(v_msgData_344_, 1, v___x_343_);
v___x_345_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_344_, v_macroStack_324_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_350_, lean_object* v_macroStack_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_350_, v_macroStack_351_, v___y_352_);
lean_dec_ref(v___y_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_ref_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v_macroStack_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_ref_363_ = lean_ctor_get(v___y_360_, 5);
v___x_364_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_355_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v___x_364_);
v_macroStack_366_ = lean_ctor_get(v___y_356_, 1);
v___x_367_ = l_Lean_Elab_getBetterRef(v_ref_363_, v_macroStack_366_);
lean_inc(v_macroStack_366_);
v___x_368_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_365_, v_macroStack_366_, v___y_360_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_377_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_367_);
lean_ctor_set(v___x_373_, 1, v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 1);
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_387_, size_t v_i_388_, size_t v_stop_389_, lean_object* v_b_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_eq(v_i_388_, v_stop_389_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; size_t v___x_394_; size_t v___x_395_; 
v___x_392_ = lean_array_uget_borrowed(v_as_387_, v_i_388_);
lean_inc(v___x_392_);
v___x_393_ = l_Lean_NameSet_insert(v_b_390_, v___x_392_);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_add(v_i_388_, v___x_394_);
v_i_388_ = v___x_395_;
v_b_390_ = v___x_393_;
goto _start;
}
else
{
return v_b_390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_397_, lean_object* v_i_398_, lean_object* v_stop_399_, lean_object* v_b_400_){
_start:
{
size_t v_i_boxed_401_; size_t v_stop_boxed_402_; lean_object* v_res_403_; 
v_i_boxed_401_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_stop_boxed_402_ = lean_unbox_usize(v_stop_399_);
lean_dec(v_stop_399_);
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_397_, v_i_boxed_401_, v_stop_boxed_402_, v_b_400_);
lean_dec_ref(v_as_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_404_, size_t v_i_405_, lean_object* v_bs_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_lt(v_i_405_, v_sz_404_);
if (v___x_407_ == 0)
{
return v_bs_406_;
}
else
{
lean_object* v_v_408_; lean_object* v___x_409_; lean_object* v_bs_x27_410_; lean_object* v___x_411_; size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v_v_408_ = lean_array_uget(v_bs_406_, v_i_405_);
v___x_409_ = lean_unsigned_to_nat(0u);
v_bs_x27_410_ = lean_array_uset(v_bs_406_, v_i_405_, v___x_409_);
v___x_411_ = l_Lean_TSyntax_getId(v_v_408_);
lean_dec(v_v_408_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_add(v_i_405_, v___x_412_);
v___x_414_ = lean_array_uset(v_bs_x27_410_, v_i_405_, v___x_411_);
v_i_405_ = v___x_413_;
v_bs_406_ = v___x_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_416_, lean_object* v_i_417_, lean_object* v_bs_418_){
_start:
{
size_t v_sz_boxed_419_; size_t v_i_boxed_420_; lean_object* v_res_421_; 
v_sz_boxed_419_ = lean_unbox_usize(v_sz_416_);
lean_dec(v_sz_416_);
v_i_boxed_420_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_res_421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_419_, v_i_boxed_420_, v_bs_418_);
return v_res_421_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_430_, size_t v_i_431_, lean_object* v_bs_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_bs_432_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v_bs_x27_436_; lean_object* v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v_bs_x27_436_ = lean_array_uset(v_bs_432_, v_i_431_, v___x_435_);
v___x_437_ = lean_box(0);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_431_, v___x_438_);
v___x_440_ = lean_array_uset(v_bs_x27_436_, v_i_431_, v___x_437_);
v_i_431_ = v___x_439_;
v_bs_432_ = v___x_440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_442_, lean_object* v_i_443_, lean_object* v_bs_444_){
_start:
{
size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v_sz_boxed_445_ = lean_unbox_usize(v_sz_442_);
lean_dec(v_sz_442_);
v_i_boxed_446_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_445_, v_i_boxed_446_, v_bs_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_448_, uint8_t v___x_449_, lean_object* v_as_450_, size_t v_i_451_, size_t v_stop_452_, lean_object* v_b_453_){
_start:
{
lean_object* v___y_455_; uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_eq(v_i_451_, v_stop_452_);
if (v___x_459_ == 0)
{
lean_object* v_fst_460_; uint8_t v___x_461_; 
v_fst_460_ = lean_ctor_get(v_b_453_, 0);
v___x_461_ = lean_unbox(v_fst_460_);
if (v___x_461_ == 0)
{
lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_snd_462_ = lean_ctor_get(v_b_453_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_b_453_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_b_453_, 0);
lean_dec(v_unused_471_);
v___x_464_ = v_b_453_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_dec(v_b_453_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_box(v___x_448_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_462_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v___y_455_ = v___x_468_;
goto v___jp_454_;
}
}
}
else
{
lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_482_; 
v_snd_472_ = lean_ctor_get(v_b_453_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_b_453_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v_b_453_, 0);
lean_dec(v_unused_483_);
v___x_474_ = v_b_453_;
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_dec(v_b_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_476_ = lean_array_uget_borrowed(v_as_450_, v_i_451_);
lean_inc(v___x_476_);
v___x_477_ = lean_array_push(v_snd_472_, v___x_476_);
v___x_478_ = lean_box(v___x_449_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_477_);
lean_ctor_set(v___x_474_, 0, v___x_478_);
v___x_480_ = v___x_474_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_477_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v___y_455_ = v___x_480_;
goto v___jp_454_;
}
}
}
}
else
{
return v_b_453_;
}
v___jp_454_:
{
size_t v___x_456_; size_t v___x_457_; 
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_add(v_i_451_, v___x_456_);
v_i_451_ = v___x_457_;
v_b_453_ = v___y_455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v_as_486_, lean_object* v_i_487_, lean_object* v_stop_488_, lean_object* v_b_489_){
_start:
{
uint8_t v___x_279776__boxed_490_; uint8_t v___x_279777__boxed_491_; size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v___x_279776__boxed_490_ = lean_unbox(v___x_484_);
v___x_279777__boxed_491_ = lean_unbox(v___x_485_);
v_i_boxed_492_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_488_);
lean_dec(v_stop_488_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_279776__boxed_490_, v___x_279777__boxed_491_, v_as_486_, v_i_boxed_492_, v_stop_boxed_493_, v_b_489_);
lean_dec_ref(v_as_486_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_495_, lean_object* v_declName_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v___x_499_; lean_object* v_env_500_; lean_object* v___x_501_; uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_499_ = 0;
v_env_500_ = l_Lean_Environment_setExporting(v_env_495_, v___x_499_);
lean_inc(v_declName_496_);
v___x_501_ = l_Lean_mkPrivateName(v_env_500_, v_declName_496_);
v___x_502_ = 1;
lean_inc_ref(v_env_500_);
v___x_503_ = l_Lean_Environment_contains(v_env_500_, v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = l_Lean_privateToUserName(v_declName_496_);
v___x_505_ = l_Lean_Environment_contains(v_env_500_, v___x_504_, v___x_502_);
v___x_506_ = lean_box(v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___y_498_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref(v_env_500_);
lean_dec(v_declName_496_);
v___x_508_ = lean_box(v___x_503_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___y_498_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_510_, lean_object* v_declName_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_510_, v_declName_511_, v___y_512_, v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = l_Lean_maxRecDepthErrorMessage;
v___x_521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_523_ = l_Lean_MessageData_ofFormat(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_525_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_526_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_527_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_ref_527_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; 
v_a_537_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_a_537_);
v___x_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_538_, 0, v_a_537_);
lean_ctor_set(v___x_538_, 1, v___y_536_);
return v___x_538_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_540_; 
v_a_539_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_a_539_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_a_539_);
lean_ctor_set(v___x_540_, 1, v___y_536_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_541_, v___y_542_);
lean_dec_ref(v_x_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_544_, lean_object* v_stx_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_544_, v_stx_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
if (lean_obj_tag(v_a_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_a_550_ = lean_ctor_get(v___x_548_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_548_, 0);
lean_dec(v_unused_559_);
v___x_552_ = v___x_548_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_box(0);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_a_550_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_588_; 
v_val_560_ = lean_ctor_get(v_a_549_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_588_ == 0)
{
v___x_562_ = v_a_549_;
v_isShared_563_ = v_isSharedCheck_588_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v_a_549_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_588_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_snd_564_; 
v_snd_564_ = lean_ctor_get(v_val_560_, 1);
lean_inc(v_snd_564_);
lean_dec(v_val_560_);
if (lean_obj_tag(v_snd_564_) == 0)
{
lean_object* v_a_565_; lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_562_);
v_a_565_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_a_565_);
lean_dec_ref(v___x_548_);
v_a_566_ = lean_ctor_get(v_snd_564_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_snd_564_);
if (v_isSharedCheck_574_ == 0)
{
v___x_568_ = v_snd_564_;
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v_snd_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_571_, v_a_565_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
}
}
else
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_587_; 
v_a_575_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_a_575_);
lean_dec_ref(v___x_548_);
v_a_576_ = lean_ctor_get(v_snd_564_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_snd_564_);
if (v_isSharedCheck_587_ == 0)
{
v___x_578_ = v_snd_564_;
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v_snd_564_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v_a_576_);
v___x_581_ = v___x_562_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_586_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_583_, v_a_575_);
lean_dec_ref(v___x_583_);
return v___x_584_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_589_ = lean_ctor_get(v___x_548_, 0);
v_a_590_ = lean_ctor_get(v___x_548_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_548_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_inc(v_a_589_);
lean_dec(v___x_548_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_589_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_598_, lean_object* v_stx_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_598_, v_stx_599_, v___y_600_, v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_603_, lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_fileName_612_; lean_object* v_fileMap_613_; lean_object* v_options_614_; lean_object* v_currRecDepth_615_; lean_object* v_maxRecDepth_616_; lean_object* v_ref_617_; lean_object* v_currNamespace_618_; lean_object* v_openDecls_619_; lean_object* v_initHeartbeats_620_; lean_object* v_maxHeartbeats_621_; lean_object* v_quotContext_622_; lean_object* v_currMacroScope_623_; uint8_t v_diag_624_; lean_object* v_cancelTk_x3f_625_; uint8_t v_suppressElabErrors_626_; lean_object* v_inheritedTraceOptions_627_; lean_object* v_ref_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_fileName_612_ = lean_ctor_get(v___y_609_, 0);
v_fileMap_613_ = lean_ctor_get(v___y_609_, 1);
v_options_614_ = lean_ctor_get(v___y_609_, 2);
v_currRecDepth_615_ = lean_ctor_get(v___y_609_, 3);
v_maxRecDepth_616_ = lean_ctor_get(v___y_609_, 4);
v_ref_617_ = lean_ctor_get(v___y_609_, 5);
v_currNamespace_618_ = lean_ctor_get(v___y_609_, 6);
v_openDecls_619_ = lean_ctor_get(v___y_609_, 7);
v_initHeartbeats_620_ = lean_ctor_get(v___y_609_, 8);
v_maxHeartbeats_621_ = lean_ctor_get(v___y_609_, 9);
v_quotContext_622_ = lean_ctor_get(v___y_609_, 10);
v_currMacroScope_623_ = lean_ctor_get(v___y_609_, 11);
v_diag_624_ = lean_ctor_get_uint8(v___y_609_, sizeof(void*)*14);
v_cancelTk_x3f_625_ = lean_ctor_get(v___y_609_, 12);
v_suppressElabErrors_626_ = lean_ctor_get_uint8(v___y_609_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_627_ = lean_ctor_get(v___y_609_, 13);
v_ref_628_ = l_Lean_replaceRef(v_ref_603_, v_ref_617_);
lean_inc_ref(v_inheritedTraceOptions_627_);
lean_inc(v_cancelTk_x3f_625_);
lean_inc(v_currMacroScope_623_);
lean_inc(v_quotContext_622_);
lean_inc(v_maxHeartbeats_621_);
lean_inc(v_initHeartbeats_620_);
lean_inc(v_openDecls_619_);
lean_inc(v_currNamespace_618_);
lean_inc(v_maxRecDepth_616_);
lean_inc(v_currRecDepth_615_);
lean_inc_ref(v_options_614_);
lean_inc_ref(v_fileMap_613_);
lean_inc_ref(v_fileName_612_);
v___x_629_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_629_, 0, v_fileName_612_);
lean_ctor_set(v___x_629_, 1, v_fileMap_613_);
lean_ctor_set(v___x_629_, 2, v_options_614_);
lean_ctor_set(v___x_629_, 3, v_currRecDepth_615_);
lean_ctor_set(v___x_629_, 4, v_maxRecDepth_616_);
lean_ctor_set(v___x_629_, 5, v_ref_628_);
lean_ctor_set(v___x_629_, 6, v_currNamespace_618_);
lean_ctor_set(v___x_629_, 7, v_openDecls_619_);
lean_ctor_set(v___x_629_, 8, v_initHeartbeats_620_);
lean_ctor_set(v___x_629_, 9, v_maxHeartbeats_621_);
lean_ctor_set(v___x_629_, 10, v_quotContext_622_);
lean_ctor_set(v___x_629_, 11, v_currMacroScope_623_);
lean_ctor_set(v___x_629_, 12, v_cancelTk_x3f_625_);
lean_ctor_set(v___x_629_, 13, v_inheritedTraceOptions_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*14, v_diag_624_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*14 + 1, v_suppressElabErrors_626_);
v___x_630_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___x_629_, v___y_610_);
lean_dec_ref(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_631_, lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_631_, v_msg_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v_ref_631_);
return v_res_640_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_641_; double v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_float_of_nat(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_ref_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_699_; 
v_ref_653_ = lean_ctor_get(v___y_650_, 5);
v___x_654_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_699_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_699_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_699_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v_traceState_660_; lean_object* v_env_661_; lean_object* v_nextMacroScope_662_; lean_object* v_ngen_663_; lean_object* v_auxDeclNGen_664_; lean_object* v_cache_665_; lean_object* v_messages_666_; lean_object* v_infoState_667_; lean_object* v_snapshotTasks_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_698_; 
v___x_659_ = lean_st_ref_take(v___y_651_);
v_traceState_660_ = lean_ctor_get(v___x_659_, 4);
v_env_661_ = lean_ctor_get(v___x_659_, 0);
v_nextMacroScope_662_ = lean_ctor_get(v___x_659_, 1);
v_ngen_663_ = lean_ctor_get(v___x_659_, 2);
v_auxDeclNGen_664_ = lean_ctor_get(v___x_659_, 3);
v_cache_665_ = lean_ctor_get(v___x_659_, 5);
v_messages_666_ = lean_ctor_get(v___x_659_, 6);
v_infoState_667_ = lean_ctor_get(v___x_659_, 7);
v_snapshotTasks_668_ = lean_ctor_get(v___x_659_, 8);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_698_ == 0)
{
v___x_670_ = v___x_659_;
v_isShared_671_ = v_isSharedCheck_698_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_snapshotTasks_668_);
lean_inc(v_infoState_667_);
lean_inc(v_messages_666_);
lean_inc(v_cache_665_);
lean_inc(v_traceState_660_);
lean_inc(v_auxDeclNGen_664_);
lean_inc(v_ngen_663_);
lean_inc(v_nextMacroScope_662_);
lean_inc(v_env_661_);
lean_dec(v___x_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_698_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
uint64_t v_tid_672_; lean_object* v_traces_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_697_; 
v_tid_672_ = lean_ctor_get_uint64(v_traceState_660_, sizeof(void*)*1);
v_traces_673_ = lean_ctor_get(v_traceState_660_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v_traceState_660_);
if (v_isSharedCheck_697_ == 0)
{
v___x_675_ = v_traceState_660_;
v_isShared_676_ = v_isSharedCheck_697_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_traces_673_);
lean_dec(v_traceState_660_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_697_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; double v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_677_ = lean_box(0);
v___x_678_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_679_ = 0;
v___x_680_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_681_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_681_, 0, v_cls_646_);
lean_ctor_set(v___x_681_, 1, v___x_677_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
lean_ctor_set_float(v___x_681_, sizeof(void*)*3, v___x_678_);
lean_ctor_set_float(v___x_681_, sizeof(void*)*3 + 8, v___x_678_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*3 + 16, v___x_679_);
v___x_682_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_683_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v_a_655_);
lean_ctor_set(v___x_683_, 2, v___x_682_);
lean_inc(v_ref_653_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_ref_653_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_PersistentArray_push___redArg(v_traces_673_, v___x_684_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_685_);
v___x_687_ = v___x_675_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_685_);
lean_ctor_set_uint64(v_reuseFailAlloc_696_, sizeof(void*)*1, v_tid_672_);
v___x_687_ = v_reuseFailAlloc_696_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 4, v___x_687_);
v___x_689_ = v___x_670_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_env_661_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_nextMacroScope_662_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_ngen_663_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_auxDeclNGen_664_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v_cache_665_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_messages_666_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_infoState_667_);
lean_ctor_set(v_reuseFailAlloc_695_, 8, v_snapshotTasks_668_);
v___x_689_ = v_reuseFailAlloc_695_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_st_ref_set(v___y_651_, v___x_689_);
v___x_691_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_691_);
v___x_693_ = v___x_657_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_700_, v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
if (lean_obj_tag(v_as_711_) == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_box(0);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
else
{
lean_object* v_options_721_; uint8_t v_hasTrace_722_; 
v_options_721_ = lean_ctor_get(v___y_716_, 2);
v_hasTrace_722_ = lean_ctor_get_uint8(v_options_721_, sizeof(void*)*1);
if (v_hasTrace_722_ == 0)
{
lean_object* v_tail_723_; 
v_tail_723_ = lean_ctor_get(v_as_711_, 1);
lean_inc(v_tail_723_);
lean_dec_ref(v_as_711_);
v_as_711_ = v_tail_723_;
goto _start;
}
else
{
lean_object* v_head_725_; lean_object* v_tail_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v_inheritedTraceOptions_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_head_725_ = lean_ctor_get(v_as_711_, 0);
lean_inc(v_head_725_);
v_tail_726_ = lean_ctor_get(v_as_711_, 1);
lean_inc(v_tail_726_);
lean_dec_ref(v_as_711_);
v_fst_727_ = lean_ctor_get(v_head_725_, 0);
lean_inc_n(v_fst_727_, 2);
v_snd_728_ = lean_ctor_get(v_head_725_, 1);
lean_inc(v_snd_728_);
lean_dec(v_head_725_);
v_inheritedTraceOptions_729_ = lean_ctor_get(v___y_716_, 13);
v___x_730_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_731_ = l_Lean_Name_append(v___x_730_, v_fst_727_);
v___x_732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_729_, v_options_721_, v___x_731_);
lean_dec(v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_snd_728_);
lean_dec(v_fst_727_);
v_as_711_ = v_tail_726_;
goto _start;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_734_, 0, v_snd_728_);
v___x_735_ = l_Lean_MessageData_ofFormat(v___x_734_);
v___x_736_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_727_, v___x_735_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_dec_ref(v___x_736_);
v_as_711_ = v_tail_726_;
goto _start;
}
else
{
lean_dec(v_tail_726_);
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
else
{
lean_object* v_key_750_; lean_object* v_value_751_; lean_object* v_tail_752_; uint8_t v___x_753_; 
v_key_750_ = lean_ctor_get(v_x_748_, 0);
v_value_751_ = lean_ctor_get(v_x_748_, 1);
v_tail_752_ = lean_ctor_get(v_x_748_, 2);
v___x_753_ = lean_name_eq(v_key_750_, v_a_747_);
if (v___x_753_ == 0)
{
v_x_748_ = v_tail_752_;
goto _start;
}
else
{
lean_object* v___x_755_; 
lean_inc(v_value_751_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_value_751_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec(v_a_756_);
return v_res_758_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_759_; uint64_t v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(1723u);
v___x_760_ = lean_uint64_of_nat(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_buckets_763_; lean_object* v___x_764_; uint64_t v___y_766_; 
v_buckets_763_ = lean_ctor_get(v_m_761_, 1);
v___x_764_ = lean_array_get_size(v_buckets_763_);
if (lean_obj_tag(v_a_762_) == 0)
{
uint64_t v___x_780_; 
v___x_780_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_766_ = v___x_780_;
goto v___jp_765_;
}
else
{
uint64_t v_hash_781_; 
v_hash_781_ = lean_ctor_get_uint64(v_a_762_, sizeof(void*)*2);
v___y_766_ = v_hash_781_;
goto v___jp_765_;
}
v___jp_765_:
{
uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v_fold_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_767_ = 32ULL;
v___x_768_ = lean_uint64_shift_right(v___y_766_, v___x_767_);
v_fold_769_ = lean_uint64_xor(v___y_766_, v___x_768_);
v___x_770_ = 16ULL;
v___x_771_ = lean_uint64_shift_right(v_fold_769_, v___x_770_);
v___x_772_ = lean_uint64_xor(v_fold_769_, v___x_771_);
v___x_773_ = lean_uint64_to_usize(v___x_772_);
v___x_774_ = lean_usize_of_nat(v___x_764_);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_sub(v___x_774_, v___x_775_);
v___x_777_ = lean_usize_land(v___x_773_, v___x_776_);
v___x_778_ = lean_array_uget_borrowed(v_buckets_763_, v___x_777_);
v___x_779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_762_, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_m_782_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_array_get_size(v_keys_785_);
v___x_789_ = lean_nat_dec_lt(v_i_786_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_i_786_);
return v___x_789_;
}
else
{
lean_object* v_k_x27_790_; uint8_t v___x_791_; 
v_k_x27_790_ = lean_array_fget_borrowed(v_keys_785_, v_i_786_);
v___x_791_ = l_Lean_instBEqExtraModUse_beq(v_k_787_, v_k_x27_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_i_786_, v___x_792_);
lean_dec(v_i_786_);
v_i_786_ = v___x_793_;
goto _start;
}
else
{
lean_dec(v_i_786_);
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_795_, lean_object* v_i_796_, lean_object* v_k_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_795_, v_i_796_, v_k_797_);
lean_dec_ref(v_k_797_);
lean_dec_ref(v_keys_795_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; 
v___x_800_ = ((size_t)5ULL);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_shift_left(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; 
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0);
v___x_805_ = lean_usize_sub(v___x_804_, v___x_803_);
return v___x_805_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_806_, size_t v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v_es_809_; lean_object* v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v_j_814_; lean_object* v___x_815_; 
v_es_809_ = lean_ctor_get(v_x_806_, 0);
v___x_810_ = lean_box(2);
v___x_811_ = ((size_t)5ULL);
v___x_812_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1);
v___x_813_ = lean_usize_land(v_x_807_, v___x_812_);
v_j_814_ = lean_usize_to_nat(v___x_813_);
v___x_815_ = lean_array_get_borrowed(v___x_810_, v_es_809_, v_j_814_);
lean_dec(v_j_814_);
switch(lean_obj_tag(v___x_815_))
{
case 0:
{
lean_object* v_key_816_; uint8_t v___x_817_; 
v_key_816_ = lean_ctor_get(v___x_815_, 0);
v___x_817_ = l_Lean_instBEqExtraModUse_beq(v_x_808_, v_key_816_);
return v___x_817_;
}
case 1:
{
lean_object* v_node_818_; size_t v___x_819_; 
v_node_818_ = lean_ctor_get(v___x_815_, 0);
v___x_819_ = lean_usize_shift_right(v_x_807_, v___x_811_);
v_x_806_ = v_node_818_;
v_x_807_ = v___x_819_;
goto _start;
}
default: 
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
}
}
else
{
lean_object* v_ks_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_ks_822_ = lean_ctor_get(v_x_806_, 0);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_822_, v___x_823_, v_x_808_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
size_t v_x_280306__boxed_828_; uint8_t v_res_829_; lean_object* v_r_830_; 
v_x_280306__boxed_828_ = lean_unbox_usize(v_x_826_);
lean_dec(v_x_826_);
v_res_829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_825_, v_x_280306__boxed_828_, v_x_827_);
lean_dec_ref(v_x_827_);
lean_dec_ref(v_x_825_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint64_t v___x_833_; size_t v___x_834_; uint8_t v___x_835_; 
v___x_833_ = l_Lean_instHashableExtraModUse_hash(v_x_832_);
v___x_834_ = lean_uint64_to_usize(v___x_833_);
v___x_835_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_831_, v___x_834_, v_x_832_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_836_, v_x_837_);
lean_dec_ref(v_x_837_);
lean_dec_ref(v_x_836_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_843_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_844_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_843_, v___x_842_);
return v___x_844_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_851_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
lean_ctor_set(v___x_851_, 3, v___x_850_);
lean_ctor_set(v___x_851_, 4, v___x_850_);
lean_ctor_set(v___x_851_, 5, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_cls_863_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_864_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_865_ = l_Lean_Name_append(v___x_864_, v_cls_863_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_876_, uint8_t v_isMeta_877_, lean_object* v_hint_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v_env_887_; uint8_t v_isExporting_888_; lean_object* v___x_889_; lean_object* v_env_890_; lean_object* v___x_891_; lean_object* v_entry_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_886_ = lean_st_ref_get(v___y_884_);
v_env_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_env_887_);
lean_dec(v___x_886_);
v_isExporting_888_ = lean_ctor_get_uint8(v_env_887_, sizeof(void*)*8);
lean_dec_ref(v_env_887_);
v___x_889_ = lean_st_ref_get(v___y_884_);
v_env_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc_ref(v_env_890_);
lean_dec(v___x_889_);
v___x_891_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_876_);
v_entry_892_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_892_, 0, v_mod_876_);
lean_ctor_set_uint8(v_entry_892_, sizeof(void*)*1, v_isExporting_888_);
lean_ctor_set_uint8(v_entry_892_, sizeof(void*)*1 + 1, v_isMeta_877_);
v___x_893_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_894_ = lean_box(1);
v___x_895_ = lean_box(0);
v___x_938_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_891_, v___x_893_, v_env_890_, v___x_894_, v___x_895_);
v___x_939_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_938_, v_entry_892_);
lean_dec(v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v_options_940_; uint8_t v_hasTrace_941_; 
v_options_940_ = lean_ctor_get(v___y_883_, 2);
v_hasTrace_941_ = lean_ctor_get_uint8(v_options_940_, sizeof(void*)*1);
if (v_hasTrace_941_ == 0)
{
lean_dec(v_hint_878_);
lean_dec(v_mod_876_);
v___y_897_ = v___y_882_;
v___y_898_ = v___y_884_;
goto v___jp_896_;
}
else
{
lean_object* v_inheritedTraceOptions_942_; lean_object* v_cls_943_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_inheritedTraceOptions_942_ = lean_ctor_get(v___y_883_, 13);
v_cls_943_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_963_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_942_, v_options_940_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec(v_hint_878_);
lean_dec(v_mod_876_);
v___y_897_ = v___y_882_;
v___y_898_ = v___y_884_;
goto v___jp_896_;
}
else
{
lean_object* v___x_965_; lean_object* v___y_967_; 
v___x_965_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_888_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_967_ = v___x_974_;
goto v___jp_966_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_967_ = v___x_975_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc_ref(v___y_967_);
v___x_968_ = l_Lean_stringToMessageData(v___y_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_965_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
if (v_isMeta_877_ == 0)
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_950_ = v___x_971_;
v___y_951_ = v___x_972_;
goto v___jp_949_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_950_ = v___x_971_;
v___y_951_ = v___x_973_;
goto v___jp_949_;
}
}
}
v___jp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___y_945_);
lean_ctor_set(v___x_947_, 1, v___y_946_);
v___x_948_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_943_, v___x_947_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_dec_ref(v___x_948_);
v___y_897_ = v___y_882_;
v___y_898_ = v___y_884_;
goto v___jp_896_;
}
else
{
lean_dec_ref(v_entry_892_);
return v___x_948_;
}
}
v___jp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
lean_inc_ref(v___y_951_);
v___x_952_ = l_Lean_stringToMessageData(v___y_951_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___y_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_MessageData_ofName(v_mod_876_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_Name_isAnonymous(v_hint_878_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_960_ = l_Lean_MessageData_ofName(v_hint_878_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___y_945_ = v___x_957_;
v___y_946_ = v___x_961_;
goto v___jp_944_;
}
else
{
lean_object* v___x_962_; 
lean_dec(v_hint_878_);
v___x_962_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_945_ = v___x_957_;
v___y_946_ = v___x_962_;
goto v___jp_944_;
}
}
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec_ref(v_entry_892_);
lean_dec(v_hint_878_);
lean_dec(v_mod_876_);
v___x_976_ = lean_box(0);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
v___jp_896_:
{
lean_object* v___x_899_; lean_object* v_toEnvExtension_900_; lean_object* v_env_901_; lean_object* v_nextMacroScope_902_; lean_object* v_ngen_903_; lean_object* v_auxDeclNGen_904_; lean_object* v_traceState_905_; lean_object* v_messages_906_; lean_object* v_infoState_907_; lean_object* v_snapshotTasks_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_936_; 
v___x_899_ = lean_st_ref_take(v___y_898_);
v_toEnvExtension_900_ = lean_ctor_get(v___x_893_, 0);
v_env_901_ = lean_ctor_get(v___x_899_, 0);
v_nextMacroScope_902_ = lean_ctor_get(v___x_899_, 1);
v_ngen_903_ = lean_ctor_get(v___x_899_, 2);
v_auxDeclNGen_904_ = lean_ctor_get(v___x_899_, 3);
v_traceState_905_ = lean_ctor_get(v___x_899_, 4);
v_messages_906_ = lean_ctor_get(v___x_899_, 6);
v_infoState_907_ = lean_ctor_get(v___x_899_, 7);
v_snapshotTasks_908_ = lean_ctor_get(v___x_899_, 8);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v___x_899_, 5);
lean_dec(v_unused_937_);
v___x_910_ = v___x_899_;
v_isShared_911_ = v_isSharedCheck_936_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_snapshotTasks_908_);
lean_inc(v_infoState_907_);
lean_inc(v_messages_906_);
lean_inc(v_traceState_905_);
lean_inc(v_auxDeclNGen_904_);
lean_inc(v_ngen_903_);
lean_inc(v_nextMacroScope_902_);
lean_inc(v_env_901_);
lean_dec(v___x_899_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_936_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_asyncMode_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v_asyncMode_912_ = lean_ctor_get(v_toEnvExtension_900_, 2);
v___x_913_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_893_, v_env_901_, v_entry_892_, v_asyncMode_912_, v___x_895_);
v___x_914_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 5, v___x_914_);
lean_ctor_set(v___x_910_, 0, v___x_913_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_nextMacroScope_902_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_ngen_903_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_auxDeclNGen_904_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_traceState_905_);
lean_ctor_set(v_reuseFailAlloc_935_, 5, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_935_, 6, v_messages_906_);
lean_ctor_set(v_reuseFailAlloc_935_, 7, v_infoState_907_);
lean_ctor_set(v_reuseFailAlloc_935_, 8, v_snapshotTasks_908_);
v___x_916_ = v_reuseFailAlloc_935_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_mctx_919_; lean_object* v_zetaDeltaFVarIds_920_; lean_object* v_postponed_921_; lean_object* v_diag_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_933_; 
v___x_917_ = lean_st_ref_set(v___y_898_, v___x_916_);
v___x_918_ = lean_st_ref_take(v___y_897_);
v_mctx_919_ = lean_ctor_get(v___x_918_, 0);
v_zetaDeltaFVarIds_920_ = lean_ctor_get(v___x_918_, 2);
v_postponed_921_ = lean_ctor_get(v___x_918_, 3);
v_diag_922_ = lean_ctor_get(v___x_918_, 4);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v___x_918_, 1);
lean_dec(v_unused_934_);
v___x_924_ = v___x_918_;
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_diag_922_);
lean_inc(v_postponed_921_);
lean_inc(v_zetaDeltaFVarIds_920_);
lean_inc(v_mctx_919_);
lean_dec(v___x_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_mctx_919_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_zetaDeltaFVarIds_920_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_postponed_921_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_diag_922_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_st_ref_set(v___y_897_, v___x_928_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_978_, lean_object* v_isMeta_979_, lean_object* v_hint_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_isMeta_boxed_988_; lean_object* v_res_989_; 
v_isMeta_boxed_988_ = lean_unbox(v_isMeta_979_);
v_res_989_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_978_, v_isMeta_boxed_988_, v_hint_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_990_, lean_object* v_declName_991_, lean_object* v_as_992_, size_t v_sz_993_, size_t v_i_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_lt(v_i_994_, v_sz_993_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec(v_declName_991_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_b_995_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; lean_object* v_modules_1006_; lean_object* v___x_1007_; lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v_toImport_1010_; lean_object* v_module_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1005_ = l_Lean_Environment_header(v___x_990_);
v_modules_1006_ = lean_ctor_get(v___x_1005_, 3);
lean_inc_ref(v_modules_1006_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1008_ = lean_array_uget_borrowed(v_as_992_, v_i_994_);
v___x_1009_ = lean_array_get(v___x_1007_, v_modules_1006_, v_a_1008_);
lean_dec_ref(v_modules_1006_);
v_toImport_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc_ref(v_toImport_1010_);
lean_dec(v___x_1009_);
v_module_1011_ = lean_ctor_get(v_toImport_1010_, 0);
lean_inc(v_module_1011_);
lean_dec_ref(v_toImport_1010_);
v___x_1012_ = 0;
lean_inc(v_declName_991_);
v___x_1013_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1011_, v___x_1012_, v_declName_991_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; 
lean_dec_ref(v___x_1013_);
v___x_1014_ = lean_box(0);
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_add(v_i_994_, v___x_1015_);
v_i_994_ = v___x_1016_;
v_b_995_ = v___x_1014_;
goto _start;
}
else
{
lean_dec(v_declName_991_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1018_, lean_object* v_declName_1019_, lean_object* v_as_1020_, lean_object* v_sz_1021_, lean_object* v_i_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1021_);
lean_dec(v_sz_1021_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1018_, v_declName_1019_, v_as_1020_, v_sz_boxed_1031_, v_i_boxed_1032_, v_b_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_as_1020_);
lean_dec_ref(v___x_1018_);
return v_res_1033_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1037_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1038_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1037_, v___x_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1041_, uint8_t v_isMeta_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; lean_object* v_env_1054_; lean_object* v___y_1056_; lean_object* v___x_1069_; 
v___x_1050_ = lean_st_ref_get(v___y_1048_);
v_env_1054_ = lean_ctor_get(v___x_1050_, 0);
lean_inc_ref(v_env_1054_);
lean_dec(v___x_1050_);
v___x_1069_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1054_, v_declName_1041_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_dec_ref(v_env_1054_);
lean_dec(v_declName_1041_);
goto v___jp_1051_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1071_; lean_object* v_modules_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_val_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Lean_Environment_header(v_env_1054_);
v_modules_1072_ = lean_ctor_get(v___x_1071_, 3);
lean_inc_ref(v_modules_1072_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = lean_array_get_size(v_modules_1072_);
v___x_1074_ = lean_nat_dec_lt(v_val_1070_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_modules_1072_);
lean_dec(v_val_1070_);
lean_dec_ref(v_env_1054_);
lean_dec(v_declName_1041_);
goto v___jp_1051_;
}
else
{
lean_object* v___x_1075_; lean_object* v_env_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___y_1080_; 
v___x_1075_ = lean_st_ref_get(v___y_1048_);
v_env_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_env_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1078_ = lean_array_fget(v_modules_1072_, v_val_1070_);
lean_dec(v_val_1070_);
lean_dec_ref(v_modules_1072_);
if (v_isMeta_1042_ == 0)
{
lean_dec_ref(v_env_1076_);
v___y_1080_ = v_isMeta_1042_;
goto v___jp_1079_;
}
else
{
uint8_t v___x_1091_; 
lean_inc(v_declName_1041_);
v___x_1091_ = l_Lean_isMarkedMeta(v_env_1076_, v_declName_1041_);
if (v___x_1091_ == 0)
{
v___y_1080_ = v_isMeta_1042_;
goto v___jp_1079_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = 0;
v___y_1080_ = v___x_1092_;
goto v___jp_1079_;
}
}
v___jp_1079_:
{
lean_object* v_toImport_1081_; lean_object* v_module_1082_; lean_object* v___x_1083_; 
v_toImport_1081_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_toImport_1081_);
lean_dec(v___x_1078_);
v_module_1082_ = lean_ctor_get(v_toImport_1081_, 0);
lean_inc(v_module_1082_);
lean_dec_ref(v_toImport_1081_);
lean_inc(v_declName_1041_);
v___x_1083_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1082_, v___y_1080_, v_declName_1041_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v___x_1083_);
v___x_1084_ = l_Lean_indirectModUseExt;
v___x_1085_ = lean_box(1);
v___x_1086_ = lean_box(0);
lean_inc_ref(v_env_1054_);
v___x_1087_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1077_, v___x_1084_, v_env_1054_, v___x_1085_, v___x_1086_);
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1087_, v_declName_1041_);
lean_dec(v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1056_ = v___x_1089_;
goto v___jp_1055_;
}
else
{
lean_object* v_val_1090_; 
v_val_1090_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_val_1090_);
lean_dec_ref(v___x_1088_);
v___y_1056_ = v_val_1090_;
goto v___jp_1055_;
}
}
else
{
lean_dec_ref(v_env_1054_);
lean_dec(v_declName_1041_);
return v___x_1083_;
}
}
}
}
v___jp_1051_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
v___jp_1055_:
{
lean_object* v___x_1057_; size_t v_sz_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_box(0);
v_sz_1058_ = lean_array_size(v___y_1056_);
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1054_, v_declName_1041_, v___y_1056_, v_sz_1058_, v___x_1059_, v___x_1057_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_env_1054_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1060_, 0);
lean_dec(v_unused_1068_);
v___x_1062_ = v___x_1060_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1060_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1057_);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1057_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1093_, lean_object* v_isMeta_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_isMeta_boxed_1102_; lean_object* v_res_1103_; 
v_isMeta_boxed_1102_ = lean_unbox(v_isMeta_1094_);
v_res_1103_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1093_, v_isMeta_boxed_1102_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
if (lean_obj_tag(v_as_x27_1104_) == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1105_);
return v___x_1113_;
}
else
{
lean_object* v_head_1114_; lean_object* v_tail_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v_head_1114_ = lean_ctor_get(v_as_x27_1104_, 0);
v_tail_1115_ = lean_ctor_get(v_as_x27_1104_, 1);
v___x_1116_ = 1;
lean_inc(v_head_1114_);
v___x_1117_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1114_, v___x_1116_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1117_);
v___x_1118_ = lean_box(0);
v_as_x27_1104_ = v_tail_1115_;
v_b_1105_ = v___x_1118_;
goto _start;
}
else
{
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1120_, v_b_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v_as_x27_1120_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1130_, lean_object* v_currNamespace_1131_, lean_object* v_openDecls_1132_, lean_object* v_n_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = l_Lean_ResolveName_resolveNamespace(v_env_1130_, v_currNamespace_1131_, v_openDecls_1132_, v_n_1133_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1138_, lean_object* v_currNamespace_1139_, lean_object* v_openDecls_1140_, lean_object* v_n_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1138_, v_currNamespace_1139_, v_openDecls_1140_, v_n_1141_, v___y_1142_, v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_currNamespace_1145_);
lean_ctor_set(v___x_1148_, 1, v___y_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1149_, v___y_1150_, v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1153_, lean_object* v_options_1154_, lean_object* v_currNamespace_1155_, lean_object* v_openDecls_1156_, lean_object* v_n_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = l_Lean_ResolveName_resolveGlobalName(v_env_1153_, v_options_1154_, v_currNamespace_1155_, v_openDecls_1156_, v_n_1157_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___y_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1162_, lean_object* v_options_1163_, lean_object* v_currNamespace_1164_, lean_object* v_openDecls_1165_, lean_object* v_n_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1162_, v_options_1163_, v_currNamespace_1164_, v_openDecls_1165_, v_n_1166_, v___y_1167_, v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_options_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_env_1180_; lean_object* v_options_1181_; lean_object* v_currRecDepth_1182_; lean_object* v_maxRecDepth_1183_; lean_object* v_ref_1184_; lean_object* v_currNamespace_1185_; lean_object* v_openDecls_1186_; lean_object* v_quotContext_1187_; lean_object* v_currMacroScope_1188_; lean_object* v___x_1189_; lean_object* v_nextMacroScope_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v_methods_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1179_ = lean_st_ref_get(v___y_1177_);
v_env_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref_n(v_env_1180_, 4);
lean_dec(v___x_1179_);
v_options_1181_ = lean_ctor_get(v___y_1176_, 2);
v_currRecDepth_1182_ = lean_ctor_get(v___y_1176_, 3);
v_maxRecDepth_1183_ = lean_ctor_get(v___y_1176_, 4);
v_ref_1184_ = lean_ctor_get(v___y_1176_, 5);
v_currNamespace_1185_ = lean_ctor_get(v___y_1176_, 6);
v_openDecls_1186_ = lean_ctor_get(v___y_1176_, 7);
v_quotContext_1187_ = lean_ctor_get(v___y_1176_, 10);
v_currMacroScope_1188_ = lean_ctor_get(v___y_1176_, 11);
v___x_1189_ = lean_st_ref_get(v___y_1177_);
v_nextMacroScope_1190_ = lean_ctor_get(v___x_1189_, 1);
lean_inc(v_nextMacroScope_1190_);
lean_dec(v___x_1189_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1191_, 0, v_env_1180_);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1192_, 0, v_env_1180_);
lean_inc_n(v_openDecls_1186_, 2);
lean_inc_n(v_currNamespace_1185_, 3);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1193_, 0, v_env_1180_);
lean_closure_set(v___f_1193_, 1, v_currNamespace_1185_);
lean_closure_set(v___f_1193_, 2, v_openDecls_1186_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1194_, 0, v_currNamespace_1185_);
lean_inc_ref(v_options_1181_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1195_, 0, v_env_1180_);
lean_closure_set(v___f_1195_, 1, v_options_1181_);
lean_closure_set(v___f_1195_, 2, v_currNamespace_1185_);
lean_closure_set(v___f_1195_, 3, v_openDecls_1186_);
v_methods_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1196_, 0, v___f_1191_);
lean_ctor_set(v_methods_1196_, 1, v___f_1194_);
lean_ctor_set(v_methods_1196_, 2, v___f_1192_);
lean_ctor_set(v_methods_1196_, 3, v___f_1193_);
lean_ctor_set(v_methods_1196_, 4, v___f_1195_);
lean_inc(v_ref_1184_);
lean_inc(v_maxRecDepth_1183_);
lean_inc(v_currRecDepth_1182_);
lean_inc(v_currMacroScope_1188_);
lean_inc(v_quotContext_1187_);
v___x_1197_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1197_, 0, v_methods_1196_);
lean_ctor_set(v___x_1197_, 1, v_quotContext_1187_);
lean_ctor_set(v___x_1197_, 2, v_currMacroScope_1188_);
lean_ctor_set(v___x_1197_, 3, v_currRecDepth_1182_);
lean_ctor_set(v___x_1197_, 4, v_maxRecDepth_1183_);
lean_ctor_set(v___x_1197_, 5, v_ref_1184_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_nextMacroScope_1190_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
lean_ctor_set(v___x_1199_, 2, v___x_1198_);
v___x_1200_ = lean_apply_2(v_x_1171_, v___x_1197_, v___x_1199_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_a_1202_; lean_object* v_macroScope_1203_; lean_object* v_traceMsgs_1204_; lean_object* v_expandedMacroDecls_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_a_1201_);
v_a_1202_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1200_);
v_macroScope_1203_ = lean_ctor_get(v_a_1201_, 0);
lean_inc(v_macroScope_1203_);
v_traceMsgs_1204_ = lean_ctor_get(v_a_1201_, 1);
lean_inc(v_traceMsgs_1204_);
v_expandedMacroDecls_1205_ = lean_ctor_get(v_a_1201_, 2);
lean_inc(v_expandedMacroDecls_1205_);
lean_dec(v_a_1201_);
v___x_1206_ = lean_box(0);
v___x_1207_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1205_, v___x_1206_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v_expandedMacroDecls_1205_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1208_; lean_object* v_env_1209_; lean_object* v_ngen_1210_; lean_object* v_auxDeclNGen_1211_; lean_object* v_traceState_1212_; lean_object* v_cache_1213_; lean_object* v_messages_1214_; lean_object* v_infoState_1215_; lean_object* v_snapshotTasks_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___x_1207_);
v___x_1208_ = lean_st_ref_take(v___y_1177_);
v_env_1209_ = lean_ctor_get(v___x_1208_, 0);
v_ngen_1210_ = lean_ctor_get(v___x_1208_, 2);
v_auxDeclNGen_1211_ = lean_ctor_get(v___x_1208_, 3);
v_traceState_1212_ = lean_ctor_get(v___x_1208_, 4);
v_cache_1213_ = lean_ctor_get(v___x_1208_, 5);
v_messages_1214_ = lean_ctor_get(v___x_1208_, 6);
v_infoState_1215_ = lean_ctor_get(v___x_1208_, 7);
v_snapshotTasks_1216_ = lean_ctor_get(v___x_1208_, 8);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1243_);
v___x_1218_ = v___x_1208_;
v_isShared_1219_ = v_isSharedCheck_1242_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snapshotTasks_1216_);
lean_inc(v_infoState_1215_);
lean_inc(v_messages_1214_);
lean_inc(v_cache_1213_);
lean_inc(v_traceState_1212_);
lean_inc(v_auxDeclNGen_1211_);
lean_inc(v_ngen_1210_);
lean_inc(v_env_1209_);
lean_dec(v___x_1208_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1242_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v_macroScope_1203_);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_env_1209_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_macroScope_1203_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_ngen_1210_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_auxDeclNGen_1211_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_traceState_1212_);
lean_ctor_set(v_reuseFailAlloc_1241_, 5, v_cache_1213_);
lean_ctor_set(v_reuseFailAlloc_1241_, 6, v_messages_1214_);
lean_ctor_set(v_reuseFailAlloc_1241_, 7, v_infoState_1215_);
lean_ctor_set(v_reuseFailAlloc_1241_, 8, v_snapshotTasks_1216_);
v___x_1221_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_st_ref_set(v___y_1177_, v___x_1221_);
v___x_1223_ = l_List_reverse___redArg(v_traceMsgs_1204_);
v___x_1224_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1223_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1232_);
v___x_1226_ = v___x_1224_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_dec(v___x_1224_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_a_1202_);
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1202_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1202_);
v_a_1233_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1224_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1224_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_traceMsgs_1204_);
lean_dec(v_macroScope_1203_);
lean_dec(v_a_1202_);
v_a_1244_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1207_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1207_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1252_; 
v_a_1252_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1200_);
if (lean_obj_tag(v_a_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_a_1253_ = lean_ctor_get(v_a_1252_, 0);
lean_inc(v_a_1253_);
v_a_1254_ = lean_ctor_get(v_a_1252_, 1);
lean_inc_ref(v_a_1254_);
lean_dec_ref(v_a_1252_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1256_ = lean_string_dec_eq(v_a_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1254_);
v___x_1258_ = l_Lean_MessageData_ofFormat(v___x_1257_);
v___x_1259_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1253_, v___x_1258_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v_a_1253_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; 
lean_dec_ref(v_a_1254_);
v___x_1260_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1253_);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1274_, size_t v_i_1275_, lean_object* v_bs_1276_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_usize_dec_lt(v_i_1275_, v_sz_1274_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_bs_1276_);
return v___x_1278_;
}
else
{
lean_object* v_v_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_v_1279_ = lean_array_uget(v_bs_1276_, v_i_1275_);
v___x_1280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1279_);
v___x_1281_ = l_Lean_Syntax_isOfKind(v_v_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_v_1279_);
lean_dec_ref(v_bs_1276_);
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = l_Lean_Syntax_getArg(v_v_1279_, v___x_1283_);
v___x_1285_ = l_Lean_Syntax_isOfKind(v___x_1284_, v___x_1280_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v_v_1279_);
lean_dec_ref(v_bs_1276_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; lean_object* v_bs_x27_1288_; lean_object* v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1287_ = lean_unsigned_to_nat(3u);
v_bs_x27_1288_ = lean_array_uset(v_bs_1276_, v_i_1275_, v___x_1283_);
v___x_1289_ = l_Lean_Syntax_getArg(v_v_1279_, v___x_1287_);
lean_dec(v_v_1279_);
v___x_1290_ = ((size_t)1ULL);
v___x_1291_ = lean_usize_add(v_i_1275_, v___x_1290_);
v___x_1292_ = lean_array_uset(v_bs_x27_1288_, v_i_1275_, v___x_1289_);
v_i_1275_ = v___x_1291_;
v_bs_1276_ = v___x_1292_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1294_, lean_object* v_i_1295_, lean_object* v_bs_1296_){
_start:
{
size_t v_sz_boxed_1297_; size_t v_i_boxed_1298_; lean_object* v_res_1299_; 
v_sz_boxed_1297_ = lean_unbox_usize(v_sz_1294_);
lean_dec(v_sz_1294_);
v_i_boxed_1298_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1297_, v_i_boxed_1298_, v_bs_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1312_, size_t v_i_1313_, lean_object* v_bs_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_usize_dec_lt(v_i_1313_, v_sz_1312_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_bs_1314_);
return v___x_1316_;
}
else
{
lean_object* v_v_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_v_1317_ = lean_array_uget(v_bs_1314_, v_i_1313_);
v___x_1318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1317_);
v___x_1319_ = l_Lean_Syntax_isOfKind(v_v_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_v_1317_);
lean_dec_ref(v_bs_1314_);
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = l_Lean_Syntax_getArg(v_v_1317_, v___x_1321_);
v___x_1323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1324_ = l_Lean_Syntax_isOfKind(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec(v_v_1317_);
lean_dec_ref(v_bs_1314_);
v___x_1325_ = lean_box(0);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_bs_x27_1328_; lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1326_ = lean_unsigned_to_nat(3u);
v___x_1327_ = lean_unsigned_to_nat(0u);
v_bs_x27_1328_ = lean_array_uset(v_bs_1314_, v_i_1313_, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_getArg(v_v_1317_, v___x_1326_);
lean_dec(v_v_1317_);
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_add(v_i_1313_, v___x_1330_);
v___x_1332_ = lean_array_uset(v_bs_x27_1328_, v_i_1313_, v___x_1329_);
v_i_1313_ = v___x_1331_;
v_bs_1314_ = v___x_1332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1334_, lean_object* v_i_1335_, lean_object* v_bs_1336_){
_start:
{
size_t v_sz_boxed_1337_; size_t v_i_boxed_1338_; lean_object* v_res_1339_; 
v_sz_boxed_1337_ = lean_unbox_usize(v_sz_1334_);
lean_dec(v_sz_1334_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1337_, v_i_boxed_1338_, v_bs_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1346_, size_t v_i_1347_, lean_object* v_bs_1348_){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_bs_1348_);
return v___x_1350_;
}
else
{
lean_object* v_v_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_v_1351_ = lean_array_uget(v_bs_1348_, v_i_1347_);
v___x_1352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1351_);
v___x_1353_ = l_Lean_Syntax_isOfKind(v_v_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec(v_v_1351_);
lean_dec_ref(v_bs_1348_);
v___x_1354_ = lean_box(0);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v_bs_x27_1356_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v_bs_x27_1356_ = lean_array_uset(v_bs_1348_, v_i_1347_, v___x_1355_);
v___x_1363_ = l_Lean_Syntax_getArg(v_v_1351_, v___x_1355_);
lean_dec(v_v_1351_);
v___x_1364_ = l_Lean_Syntax_isNone(v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_unsigned_to_nat(2u);
v___x_1366_ = l_Lean_Syntax_matchesNull(v___x_1363_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref(v_bs_x27_1356_);
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
else
{
goto v___jp_1357_;
}
}
else
{
lean_dec(v___x_1363_);
goto v___jp_1357_;
}
v___jp_1357_:
{
lean_object* v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_i_1347_, v___x_1359_);
v___x_1361_ = lean_array_uset(v_bs_x27_1356_, v_i_1347_, v___x_1358_);
v_i_1347_ = v___x_1360_;
v_bs_1348_ = v___x_1361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1368_, lean_object* v_i_1369_, lean_object* v_bs_1370_){
_start:
{
size_t v_sz_boxed_1371_; size_t v_i_boxed_1372_; lean_object* v_res_1373_; 
v_sz_boxed_1371_ = lean_unbox_usize(v_sz_1368_);
lean_dec(v_sz_1368_);
v_i_boxed_1372_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1371_, v_i_boxed_1372_, v_bs_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1374_, size_t v_i_1375_, lean_object* v_bs_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_lt(v_i_1375_, v_sz_1374_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_bs_1376_);
return v___x_1378_;
}
else
{
lean_object* v_v_1379_; lean_object* v___x_1380_; lean_object* v_bs_x27_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v_v_1379_ = lean_array_uget(v_bs_1376_, v_i_1375_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v_bs_x27_1381_ = lean_array_uset(v_bs_1376_, v_i_1375_, v___x_1380_);
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_add(v_i_1375_, v___x_1382_);
v___x_1384_ = lean_array_uset(v_bs_x27_1381_, v_i_1375_, v_v_1379_);
v_i_1375_ = v___x_1383_;
v_bs_1376_ = v___x_1384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1386_, lean_object* v_i_1387_, lean_object* v_bs_1388_){
_start:
{
size_t v_sz_boxed_1389_; size_t v_i_boxed_1390_; lean_object* v_res_1391_; 
v_sz_boxed_1389_ = lean_unbox_usize(v_sz_1386_);
lean_dec(v_sz_1386_);
v_i_boxed_1390_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1389_, v_i_boxed_1390_, v_bs_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1393_, v___y_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1397_, v_x_1398_, v___y_1399_, v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_x_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1405_, lean_object* v_as_x27_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
if (lean_obj_tag(v_as_x27_1406_) == 0)
{
lean_object* v___x_1415_; 
lean_dec(v_stx_1405_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_b_1407_);
return v___x_1415_;
}
else
{
lean_object* v_head_1416_; lean_object* v_tail_1417_; lean_object* v_value_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v_b_1407_);
v_head_1416_ = lean_ctor_get(v_as_x27_1406_, 0);
v_tail_1417_ = lean_ctor_get(v_as_x27_1406_, 1);
v_value_1418_ = lean_ctor_get(v_head_1416_, 1);
v___x_1419_ = lean_box(0);
lean_inc(v_value_1418_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v_stx_1405_);
v___x_1420_ = lean_apply_8(v_value_1418_, v_stx_1405_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, lean_box(0));
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_stx_1405_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1430_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1430_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1421_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v___x_1419_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1426_);
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1453_; 
v_a_1431_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1433_ = v___x_1420_;
v_isShared_1434_ = v_isSharedCheck_1453_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1420_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1453_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___y_1438_; uint8_t v___x_1451_; 
v___x_1435_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1436_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1451_ = l_Lean_Exception_isInterrupt(v_a_1431_);
if (v___x_1451_ == 0)
{
uint8_t v___x_1452_; 
lean_inc(v_a_1431_);
v___x_1452_ = l_Lean_Exception_isRuntime(v_a_1431_);
v___y_1438_ = v___x_1452_;
goto v___jp_1437_;
}
else
{
v___y_1438_ = v___x_1451_;
goto v___jp_1437_;
}
v___jp_1437_:
{
if (v___y_1438_ == 0)
{
if (lean_obj_tag(v_a_1431_) == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_stx_1405_);
if (v_isShared_1434_ == 0)
{
v___x_1440_ = v___x_1433_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1431_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v_id_1442_; uint8_t v___x_1443_; 
v_id_1442_ = lean_ctor_get(v_a_1431_, 0);
v___x_1443_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1436_, v_id_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_stx_1405_);
if (v_isShared_1434_ == 0)
{
v___x_1445_ = v___x_1433_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1431_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_dec_ref(v_a_1431_);
lean_del_object(v___x_1433_);
v_as_x27_1406_ = v_tail_1417_;
v_b_1407_ = v___x_1435_;
goto _start;
}
}
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_stx_1405_);
if (v_isShared_1434_ == 0)
{
v___x_1449_ = v___x_1433_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1431_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1454_, lean_object* v_as_x27_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1454_, v_as_x27_1455_, v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v_as_x27_1455_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1467_, lean_object* v_rhs_x3f_1468_, lean_object* v_otherwise_x3f_1469_, lean_object* v_body_x3f_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
uint8_t v___y_1479_; uint8_t v___y_1480_; uint8_t v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v_body_1489_; lean_object* v___y_1509_; lean_object* v_otherwise_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v_rhs_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; 
if (lean_obj_tag(v_rhs_x3f_1468_) == 0)
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1522_ = v___x_1533_;
v___y_1523_ = v_a_1471_;
v___y_1524_ = v_a_1472_;
v___y_1525_ = v_a_1473_;
v___y_1526_ = v_a_1474_;
v___y_1527_ = v_a_1475_;
v___y_1528_ = v_a_1476_;
goto v___jp_1521_;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1535_; 
v_val_1534_ = lean_ctor_get(v_rhs_x3f_1468_, 0);
lean_inc(v_val_1534_);
lean_dec_ref(v_rhs_x3f_1468_);
v___x_1535_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1534_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v_rhs_1522_ = v_a_1536_;
v___y_1523_ = v_a_1471_;
v___y_1524_ = v_a_1472_;
v___y_1525_ = v_a_1473_;
v___y_1526_ = v_a_1474_;
v___y_1527_ = v_a_1475_;
v___y_1528_ = v_a_1476_;
goto v___jp_1521_;
}
else
{
lean_dec(v_body_x3f_1470_);
lean_dec(v_otherwise_x3f_1469_);
lean_dec_ref(v_reassigned_1467_);
return v___x_1535_;
}
}
v___jp_1478_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1484_, 0, v___y_1482_);
lean_ctor_set(v___x_1484_, 1, v___y_1483_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*2, v___y_1480_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*2 + 1, v___y_1479_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*2 + 2, v___y_1481_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
v___jp_1486_:
{
lean_object* v___x_1490_; lean_object* v_info_1491_; uint8_t v_breaks_1492_; uint8_t v_continues_1493_; uint8_t v_returnsEarly_1494_; lean_object* v_numRegularExits_1495_; lean_object* v_reassigns_1496_; size_t v_sz_1497_; size_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1490_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1489_, v___y_1487_);
v_info_1491_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1488_, v___x_1490_);
v_breaks_1492_ = lean_ctor_get_uint8(v_info_1491_, sizeof(void*)*2);
v_continues_1493_ = lean_ctor_get_uint8(v_info_1491_, sizeof(void*)*2 + 1);
v_returnsEarly_1494_ = lean_ctor_get_uint8(v_info_1491_, sizeof(void*)*2 + 2);
v_numRegularExits_1495_ = lean_ctor_get(v_info_1491_, 0);
lean_inc(v_numRegularExits_1495_);
v_reassigns_1496_ = lean_ctor_get(v_info_1491_, 1);
lean_inc(v_reassigns_1496_);
lean_dec_ref(v_info_1491_);
v_sz_1497_ = lean_array_size(v_reassigned_1467_);
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1497_, v___x_1498_, v_reassigned_1467_);
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_array_get_size(v___x_1499_);
v___x_1502_ = lean_nat_dec_lt(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_dec_ref(v___x_1499_);
v___y_1479_ = v_continues_1493_;
v___y_1480_ = v_breaks_1492_;
v___y_1481_ = v_returnsEarly_1494_;
v___y_1482_ = v_numRegularExits_1495_;
v___y_1483_ = v_reassigns_1496_;
goto v___jp_1478_;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_nat_dec_le(v___x_1501_, v___x_1501_);
if (v___x_1503_ == 0)
{
if (v___x_1502_ == 0)
{
lean_dec_ref(v___x_1499_);
v___y_1479_ = v_continues_1493_;
v___y_1480_ = v_breaks_1492_;
v___y_1481_ = v_returnsEarly_1494_;
v___y_1482_ = v_numRegularExits_1495_;
v___y_1483_ = v_reassigns_1496_;
goto v___jp_1478_;
}
else
{
size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_usize_of_nat(v___x_1501_);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1499_, v___x_1498_, v___x_1504_, v_reassigns_1496_);
lean_dec_ref(v___x_1499_);
v___y_1479_ = v_continues_1493_;
v___y_1480_ = v_breaks_1492_;
v___y_1481_ = v_returnsEarly_1494_;
v___y_1482_ = v_numRegularExits_1495_;
v___y_1483_ = v___x_1505_;
goto v___jp_1478_;
}
}
else
{
size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_usize_of_nat(v___x_1501_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1499_, v___x_1498_, v___x_1506_, v_reassigns_1496_);
lean_dec_ref(v___x_1499_);
v___y_1479_ = v_continues_1493_;
v___y_1480_ = v_breaks_1492_;
v___y_1481_ = v_returnsEarly_1494_;
v___y_1482_ = v_numRegularExits_1495_;
v___y_1483_ = v___x_1507_;
goto v___jp_1478_;
}
}
}
v___jp_1508_:
{
if (lean_obj_tag(v_body_x3f_1470_) == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1487_ = v_otherwise_1510_;
v___y_1488_ = v___y_1509_;
v_body_1489_ = v___x_1517_;
goto v___jp_1486_;
}
else
{
lean_object* v_val_1518_; lean_object* v___x_1519_; 
v_val_1518_ = lean_ctor_get(v_body_x3f_1470_, 0);
lean_inc(v_val_1518_);
lean_dec_ref(v_body_x3f_1470_);
v___x_1519_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1518_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v___y_1487_ = v_otherwise_1510_;
v___y_1488_ = v___y_1509_;
v_body_1489_ = v_a_1520_;
goto v___jp_1486_;
}
else
{
lean_dec_ref(v_otherwise_1510_);
lean_dec_ref(v___y_1509_);
lean_dec_ref(v_reassigned_1467_);
return v___x_1519_;
}
}
}
v___jp_1521_:
{
if (lean_obj_tag(v_otherwise_x3f_1469_) == 0)
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1509_ = v_rhs_1522_;
v_otherwise_1510_ = v___x_1529_;
v___y_1511_ = v___y_1523_;
v___y_1512_ = v___y_1524_;
v___y_1513_ = v___y_1525_;
v___y_1514_ = v___y_1526_;
v___y_1515_ = v___y_1527_;
v___y_1516_ = v___y_1528_;
goto v___jp_1508_;
}
else
{
lean_object* v_val_1530_; lean_object* v___x_1531_; 
v_val_1530_ = lean_ctor_get(v_otherwise_x3f_1469_, 0);
lean_inc(v_val_1530_);
lean_dec_ref(v_otherwise_x3f_1469_);
v___x_1531_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1530_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1531_);
v___y_1509_ = v_rhs_1522_;
v_otherwise_1510_ = v_a_1532_;
v___y_1511_ = v___y_1523_;
v___y_1512_ = v___y_1524_;
v___y_1513_ = v___y_1525_;
v___y_1514_ = v___y_1526_;
v___y_1515_ = v___y_1527_;
v___y_1516_ = v___y_1528_;
goto v___jp_1508_;
}
else
{
lean_dec_ref(v_rhs_1522_);
lean_dec(v_body_x3f_1470_);
lean_dec_ref(v_reassigned_1467_);
return v___x_1531_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1548_ = l_Lean_stringToMessageData(v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1639_, lean_object* v_decl_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v_reassigns_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1640_);
v___x_1677_ = l_Lean_Syntax_isOfKind(v_decl_1640_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1640_);
v___x_1679_ = l_Lean_Syntax_isOfKind(v_decl_1640_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1680_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1681_ = lean_box(0);
v___x_1682_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1681_, v___x_1679_);
v___x_1683_ = l_Std_Format_defWidth;
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = l_Std_Format_pretty(v___x_1682_, v___x_1683_, v___x_1684_, v___x_1684_);
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1680_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1687_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v_pattern_1690_; lean_object* v___y_1692_; lean_object* v_otherwise_x3f_1693_; lean_object* v_body_x3f_x3f_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v_body_x3f_x3f_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___x_1724_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1689_ = lean_unsigned_to_nat(0u);
v_pattern_1690_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1689_);
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1763_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1724_);
v___x_1764_ = l_Lean_Syntax_isNone(v___x_1763_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
lean_inc(v___x_1763_);
v___x_1765_ = l_Lean_Syntax_matchesNull(v___x_1763_, v___x_1724_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v___x_1763_);
lean_dec(v_pattern_1690_);
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1767_ = lean_box(0);
v___x_1768_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1767_, v___x_1765_);
v___x_1769_ = l_Std_Format_defWidth;
v___x_1770_ = l_Std_Format_pretty(v___x_1768_, v___x_1769_, v___x_1689_, v___x_1689_);
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1766_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1772_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = l_Lean_Syntax_getArg(v___x_1763_, v___x_1689_);
lean_dec(v___x_1763_);
v___x_1775_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1776_ = l_Lean_Syntax_isOfKind(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v_pattern_1690_);
v___x_1777_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1778_ = lean_box(0);
v___x_1779_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1778_, v___x_1776_);
v___x_1780_ = l_Std_Format_defWidth;
v___x_1781_ = l_Std_Format_pretty(v___x_1779_, v___x_1780_, v___x_1689_, v___x_1689_);
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1777_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1783_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1784_;
}
else
{
v___y_1726_ = v_a_1641_;
v___y_1727_ = v_a_1642_;
v___y_1728_ = v_a_1643_;
v___y_1729_ = v_a_1644_;
v___y_1730_ = v_a_1645_;
v___y_1731_ = v_a_1646_;
goto v___jp_1725_;
}
}
}
else
{
lean_dec(v___x_1763_);
v___y_1726_ = v_a_1641_;
v___y_1727_ = v_a_1642_;
v___y_1728_ = v_a_1643_;
v___y_1729_ = v_a_1644_;
v___y_1730_ = v_a_1645_;
v___y_1731_ = v_a_1646_;
goto v___jp_1725_;
}
v___jp_1691_:
{
if (v_reassignment_1639_ == 0)
{
lean_object* v___x_1701_; 
lean_dec(v_pattern_1690_);
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1661_ = v_body_x3f_x3f_1694_;
v___y_1662_ = v_otherwise_x3f_1693_;
v___y_1663_ = v___y_1692_;
v_reassigns_1664_ = v___x_1701_;
v___y_1665_ = v___y_1695_;
v___y_1666_ = v___y_1696_;
v___y_1667_ = v___y_1697_;
v___y_1668_ = v___y_1698_;
v___y_1669_ = v___y_1699_;
v___y_1670_ = v___y_1700_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1690_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___y_1661_ = v_body_x3f_x3f_1694_;
v___y_1662_ = v_otherwise_x3f_1693_;
v___y_1663_ = v___y_1692_;
v_reassigns_1664_ = v_a_1703_;
v___y_1665_ = v___y_1695_;
v___y_1666_ = v___y_1696_;
v___y_1667_ = v___y_1697_;
v___y_1668_ = v___y_1698_;
v___y_1669_ = v___y_1699_;
v___y_1670_ = v___y_1700_;
goto v___jp_1660_;
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_body_x3f_x3f_1694_);
lean_dec(v_otherwise_x3f_1693_);
lean_dec(v___y_1692_);
v_a_1704_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1702_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
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
v___jp_1712_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___y_1713_);
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_body_x3f_x3f_1715_);
v___y_1692_ = v___y_1714_;
v_otherwise_x3f_1693_ = v___x_1722_;
v_body_x3f_x3f_1694_ = v___x_1723_;
v___y_1695_ = v___y_1716_;
v___y_1696_ = v___y_1717_;
v___y_1697_ = v___y_1718_;
v___y_1698_ = v___y_1719_;
v___y_1699_ = v___y_1720_;
v___y_1700_ = v___y_1721_;
goto v___jp_1691_;
}
v___jp_1725_:
{
lean_object* v___x_1732_; lean_object* v_rhs_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1732_ = lean_unsigned_to_nat(3u);
v_rhs_1733_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1732_);
v___x_1734_ = lean_unsigned_to_nat(4u);
v___x_1735_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1734_);
v___x_1736_ = l_Lean_Syntax_isNone(v___x_1735_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
lean_inc(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_matchesNull(v___x_1735_, v___x_1732_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v___x_1735_);
lean_dec(v_rhs_1733_);
lean_dec(v_pattern_1690_);
v___x_1738_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1739_ = lean_box(0);
v___x_1740_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1739_, v___x_1737_);
v___x_1741_ = l_Std_Format_defWidth;
v___x_1742_ = l_Std_Format_pretty(v___x_1740_, v___x_1741_, v___x_1689_, v___x_1689_);
v___x_1743_ = l_Lean_stringToMessageData(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1738_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1744_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v_otherwise_x3f_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1746_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1747_ = l_Lean_Syntax_getArg(v___x_1735_, v___x_1724_);
v___x_1748_ = l_Lean_Syntax_getArg(v___x_1735_, v___x_1746_);
lean_dec(v___x_1735_);
v___x_1749_ = l_Lean_Syntax_isNone(v___x_1748_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
lean_inc(v___x_1748_);
v___x_1750_ = l_Lean_Syntax_matchesNull(v___x_1748_, v___x_1724_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v___x_1748_);
lean_dec(v_otherwise_x3f_1747_);
lean_dec(v_rhs_1733_);
lean_dec(v_pattern_1690_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1752_ = lean_box(0);
v___x_1753_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1752_, v___x_1750_);
v___x_1754_ = l_Std_Format_defWidth;
v___x_1755_ = l_Std_Format_pretty(v___x_1753_, v___x_1754_, v___x_1689_, v___x_1689_);
v___x_1756_ = l_Lean_stringToMessageData(v___x_1755_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1751_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1757_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1758_;
}
else
{
lean_object* v_body_x3f_x3f_1759_; lean_object* v___x_1760_; 
lean_dec(v_decl_1640_);
v_body_x3f_x3f_1759_ = l_Lean_Syntax_getArg(v___x_1748_, v___x_1689_);
lean_dec(v___x_1748_);
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_body_x3f_x3f_1759_);
v___y_1713_ = v_otherwise_x3f_1747_;
v___y_1714_ = v_rhs_1733_;
v_body_x3f_x3f_1715_ = v___x_1760_;
v___y_1716_ = v___y_1726_;
v___y_1717_ = v___y_1727_;
v___y_1718_ = v___y_1728_;
v___y_1719_ = v___y_1729_;
v___y_1720_ = v___y_1730_;
v___y_1721_ = v___y_1731_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_1761_; 
lean_dec(v___x_1748_);
lean_dec(v_decl_1640_);
v___x_1761_ = lean_box(0);
v___y_1713_ = v_otherwise_x3f_1747_;
v___y_1714_ = v_rhs_1733_;
v_body_x3f_x3f_1715_ = v___x_1761_;
v___y_1716_ = v___y_1726_;
v___y_1717_ = v___y_1727_;
v___y_1718_ = v___y_1728_;
v___y_1719_ = v___y_1729_;
v___y_1720_ = v___y_1730_;
v___y_1721_ = v___y_1731_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v___x_1735_);
lean_dec(v_decl_1640_);
v___x_1762_ = lean_box(0);
v___y_1692_ = v_rhs_1733_;
v_otherwise_x3f_1693_ = v___x_1762_;
v_body_x3f_x3f_1694_ = v___x_1762_;
v___y_1695_ = v___y_1726_;
v___y_1696_ = v___y_1727_;
v___y_1697_ = v___y_1728_;
v___y_1698_ = v___y_1729_;
v___y_1699_ = v___y_1730_;
v___y_1700_ = v___y_1731_;
goto v___jp_1691_;
}
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v_x_1786_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1785_ = lean_unsigned_to_nat(0u);
v_x_1786_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1785_);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1786_);
v___x_1801_ = l_Lean_Syntax_isOfKind(v_x_1786_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_x_1786_);
v___x_1802_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1803_ = lean_box(0);
v___x_1804_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1803_, v___x_1801_);
v___x_1805_ = l_Std_Format_defWidth;
v___x_1806_ = l_Std_Format_pretty(v___x_1804_, v___x_1805_, v___x_1785_, v___x_1785_);
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1802_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1808_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1810_);
v___x_1812_ = l_Lean_Syntax_isNone(v___x_1811_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; 
lean_inc(v___x_1811_);
v___x_1813_ = l_Lean_Syntax_matchesNull(v___x_1811_, v___x_1810_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v___x_1811_);
lean_dec(v_x_1786_);
v___x_1814_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1815_ = lean_box(0);
v___x_1816_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1815_, v___x_1813_);
v___x_1817_ = l_Std_Format_defWidth;
v___x_1818_ = l_Std_Format_pretty(v___x_1816_, v___x_1817_, v___x_1785_, v___x_1785_);
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1814_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1820_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1822_ = l_Lean_Syntax_getArg(v___x_1811_, v___x_1785_);
lean_dec(v___x_1811_);
v___x_1823_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1824_ = l_Lean_Syntax_isOfKind(v___x_1822_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v_x_1786_);
v___x_1825_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1826_ = lean_box(0);
v___x_1827_ = l_Lean_Syntax_formatStx(v_decl_1640_, v___x_1826_, v___x_1824_);
v___x_1828_ = l_Std_Format_defWidth;
v___x_1829_ = l_Std_Format_pretty(v___x_1827_, v___x_1828_, v___x_1785_, v___x_1785_);
v___x_1830_ = l_Lean_stringToMessageData(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1825_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1831_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1832_;
}
else
{
v___y_1788_ = v_a_1641_;
v___y_1789_ = v_a_1642_;
v___y_1790_ = v_a_1643_;
v___y_1791_ = v_a_1644_;
v___y_1792_ = v_a_1645_;
v___y_1793_ = v_a_1646_;
goto v___jp_1787_;
}
}
}
else
{
lean_dec(v___x_1811_);
v___y_1788_ = v_a_1641_;
v___y_1789_ = v_a_1642_;
v___y_1790_ = v_a_1643_;
v___y_1791_ = v_a_1644_;
v___y_1792_ = v_a_1645_;
v___y_1793_ = v_a_1646_;
goto v___jp_1787_;
}
}
v___jp_1787_:
{
lean_object* v___x_1794_; lean_object* v_rhs_1795_; 
v___x_1794_ = lean_unsigned_to_nat(3u);
v_rhs_1795_ = l_Lean_Syntax_getArg(v_decl_1640_, v___x_1794_);
lean_dec(v_decl_1640_);
if (v_reassignment_1639_ == 0)
{
lean_object* v___x_1796_; 
lean_dec(v_x_1786_);
v___x_1796_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1649_ = v___y_1793_;
v___y_1650_ = v___y_1788_;
v___y_1651_ = v___y_1791_;
v___y_1652_ = v___y_1789_;
v___y_1653_ = v___y_1792_;
v___y_1654_ = v___y_1790_;
v___y_1655_ = v_rhs_1795_;
v___y_1656_ = v___x_1796_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_unsigned_to_nat(1u);
v___x_1798_ = lean_mk_empty_array_with_capacity(v___x_1797_);
v___x_1799_ = lean_array_push(v___x_1798_, v_x_1786_);
v___y_1649_ = v___y_1793_;
v___y_1650_ = v___y_1788_;
v___y_1651_ = v___y_1791_;
v___y_1652_ = v___y_1789_;
v___y_1653_ = v___y_1792_;
v___y_1654_ = v___y_1790_;
v___y_1655_ = v_rhs_1795_;
v___y_1656_ = v___x_1799_;
goto v___jp_1648_;
}
}
}
v___jp_1648_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___y_1655_);
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1656_, v___x_1657_, v___x_1658_, v___x_1658_, v___y_1650_, v___y_1652_, v___y_1654_, v___y_1651_, v___y_1653_, v___y_1649_);
return v___x_1659_;
}
v___jp_1660_:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___y_1663_);
if (lean_obj_tag(v___y_1661_) == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_box(0);
v___x_1673_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1664_, v___x_1671_, v___y_1662_, v___x_1672_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1673_;
}
else
{
lean_object* v_val_1674_; lean_object* v___x_1675_; 
v_val_1674_ = lean_ctor_get(v___y_1661_, 0);
lean_inc(v_val_1674_);
lean_dec_ref(v___y_1661_);
v___x_1675_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1664_, v___x_1671_, v___y_1662_, v_val_1674_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1935_, size_t v_sz_1936_, size_t v_i_1937_, lean_object* v_b_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_usize_dec_lt(v_i_1937_, v_sz_1936_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_b_1938_);
return v___x_1947_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1949_; 
v_a_1948_ = lean_array_uget_borrowed(v_as_1935_, v_i_1937_);
lean_inc(v_a_1948_);
v___x_1949_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1948_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1950_, v_b_1938_);
v___x_1952_ = ((size_t)1ULL);
v___x_1953_ = lean_usize_add(v_i_1937_, v___x_1952_);
v_i_1937_ = v___x_1953_;
v_b_1938_ = v___x_1951_;
goto _start;
}
else
{
lean_dec_ref(v_b_1938_);
return v___x_1949_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_1984_, lean_object* v_as_1985_, size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_b_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_a_1997_; uint8_t v___x_2001_; 
v___x_2001_ = lean_usize_dec_lt(v_i_1987_, v_sz_1986_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_b_1988_);
return v___x_2002_;
}
else
{
lean_object* v___x_2003_; lean_object* v_a_2004_; uint8_t v___x_2005_; 
v___x_2003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2004_ = lean_array_uget_borrowed(v_as_1985_, v_i_1987_);
lean_inc(v_a_2004_);
v___x_2005_ = l_Lean_Syntax_isOfKind(v_a_2004_, v___x_2003_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_dec_ref(v___x_2006_);
v_a_1997_ = v_b_1988_;
goto v___jp_1996_;
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v_b_1988_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___y_2018_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_unsigned_to_nat(3u);
v___x_2035_ = l_Lean_Syntax_getArg(v_a_2004_, v___x_2015_);
v___x_2036_ = l_Lean_Syntax_getArgs(v___x_2035_);
lean_dec(v___x_2035_);
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2039_ = lean_array_get_size(v___x_2036_);
v___x_2040_ = lean_nat_dec_lt(v___x_2037_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v___x_2036_);
v___y_2018_ = v___x_2038_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2041_ = lean_box(v___x_2005_);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2038_);
v___x_2043_ = lean_nat_dec_le(v___x_2039_, v___x_2039_);
if (v___x_2043_ == 0)
{
if (v___x_2040_ == 0)
{
lean_dec_ref(v___x_2042_);
lean_dec_ref(v___x_2036_);
v___y_2018_ = v___x_2038_;
goto v___jp_2017_;
}
else
{
size_t v___x_2044_; size_t v___x_2045_; lean_object* v___x_2046_; lean_object* v_snd_2047_; 
v___x_2044_ = ((size_t)0ULL);
v___x_2045_ = lean_usize_of_nat(v___x_2039_);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2005_, v___x_1984_, v___x_2036_, v___x_2044_, v___x_2045_, v___x_2042_);
lean_dec_ref(v___x_2036_);
v_snd_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v___y_2018_ = v_snd_2047_;
goto v___jp_2017_;
}
}
else
{
size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; lean_object* v_snd_2051_; 
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = lean_usize_of_nat(v___x_2039_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2005_, v___x_1984_, v___x_2036_, v___x_2048_, v___x_2049_, v___x_2042_);
lean_dec_ref(v___x_2036_);
v_snd_2051_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_snd_2051_);
lean_dec_ref(v___x_2050_);
v___y_2018_ = v_snd_2051_;
goto v___jp_2017_;
}
}
v___jp_2017_:
{
size_t v_sz_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v_sz_2019_ = lean_array_size(v___y_2018_);
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2019_, v___x_2020_, v___y_2018_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref(v___x_2022_);
v_a_1997_ = v_b_1988_;
goto v___jp_1996_;
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_b_1988_);
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref(v___x_2021_);
v___x_2031_ = l_Lean_Syntax_getArg(v_a_2004_, v___x_2016_);
v___x_2032_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2031_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_1988_, v_a_2033_);
v_a_1997_ = v___x_2034_;
goto v___jp_1996_;
}
else
{
lean_dec_ref(v_b_1988_);
return v___x_2032_;
}
}
}
}
}
v___jp_1996_:
{
size_t v___x_1998_; size_t v___x_1999_; 
v___x_1998_ = ((size_t)1ULL);
v___x_1999_ = lean_usize_add(v_i_1987_, v___x_1998_);
v_i_1987_ = v___x_1999_;
v_b_1988_ = v_a_1997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2052_, size_t v_sz_2053_, size_t v_i_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_a_2064_; uint8_t v___x_2068_; 
v___x_2068_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_b_2055_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v_a_2071_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2070_ = lean_unsigned_to_nat(0u);
v_a_2071_ = lean_array_uget_borrowed(v_as_2052_, v_i_2054_);
v___x_2084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2071_);
v___x_2085_ = l_Lean_Syntax_isOfKind(v_a_2071_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2071_);
v___x_2087_ = l_Lean_Syntax_isOfKind(v_a_2071_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2088_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2089_ = lean_box(0);
lean_inc(v_a_2071_);
v___x_2090_ = l_Lean_Syntax_formatStx(v_a_2071_, v___x_2089_, v___x_2087_);
v___x_2091_ = l_Std_Format_defWidth;
v___x_2092_ = l_Std_Format_pretty(v___x_2090_, v___x_2091_, v___x_2070_, v___x_2070_);
v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2088_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2094_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref(v___x_2095_);
v_a_2064_ = v_b_2055_;
goto v___jp_2063_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_b_2055_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = l_Lean_Syntax_getArg(v_a_2071_, v___x_2104_);
v___x_2106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2105_);
v___x_2107_ = l_Lean_Syntax_isOfKind(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v___x_2105_);
v___x_2108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2109_ = lean_box(0);
lean_inc(v_a_2071_);
v___x_2110_ = l_Lean_Syntax_formatStx(v_a_2071_, v___x_2109_, v___x_2107_);
v___x_2111_ = l_Std_Format_defWidth;
v___x_2112_ = l_Std_Format_pretty(v___x_2110_, v___x_2111_, v___x_2070_, v___x_2070_);
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2108_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2114_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_dec_ref(v___x_2115_);
v_a_2064_ = v_b_2055_;
goto v___jp_2063_;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_b_2055_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; size_t v_sz_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2124_ = l_Lean_Syntax_getArg(v___x_2105_, v___x_2070_);
lean_dec(v___x_2105_);
v___x_2125_ = l_Lean_Syntax_getArgs(v___x_2124_);
lean_dec(v___x_2124_);
v_sz_2126_ = lean_array_size(v___x_2125_);
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2085_, v___x_2125_, v_sz_2126_, v___x_2127_, v_b_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec_ref(v___x_2125_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v_a_2064_ = v_a_2129_;
goto v___jp_2063_;
}
else
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2130_ = lean_unsigned_to_nat(2u);
v___x_2131_ = l_Lean_Syntax_getArg(v_a_2071_, v___x_2130_);
v___x_2132_ = l_Lean_Syntax_isNone(v___x_2131_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Lean_Syntax_matchesNull(v___x_2131_, v___x_2130_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2134_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2135_ = lean_box(0);
lean_inc(v_a_2071_);
v___x_2136_ = l_Lean_Syntax_formatStx(v_a_2071_, v___x_2135_, v___x_2133_);
v___x_2137_ = l_Std_Format_defWidth;
v___x_2138_ = l_Std_Format_pretty(v___x_2136_, v___x_2137_, v___x_2070_, v___x_2070_);
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
v___x_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2134_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2140_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref(v___x_2141_);
v_a_2064_ = v_b_2055_;
goto v___jp_2063_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_b_2055_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
v___y_2073_ = v___y_2056_;
v___y_2074_ = v___y_2057_;
v___y_2075_ = v___y_2058_;
v___y_2076_ = v___y_2059_;
v___y_2077_ = v___y_2060_;
v___y_2078_ = v___y_2061_;
goto v___jp_2072_;
}
}
else
{
lean_dec(v___x_2131_);
v___y_2073_ = v___y_2056_;
v___y_2074_ = v___y_2057_;
v___y_2075_ = v___y_2058_;
v___y_2076_ = v___y_2059_;
v___y_2077_ = v___y_2060_;
v___y_2078_ = v___y_2061_;
goto v___jp_2072_;
}
}
v___jp_2072_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_unsigned_to_nat(4u);
v___x_2080_ = l_Lean_Syntax_getArg(v_a_2071_, v___x_2079_);
v___x_2081_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2080_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2082_, v_b_2055_);
v_a_2064_ = v___x_2083_;
goto v___jp_2063_;
}
else
{
lean_dec_ref(v_b_2055_);
return v___x_2081_;
}
}
}
v___jp_2063_:
{
size_t v___x_2065_; size_t v___x_2066_; 
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_add(v_i_2054_, v___x_2065_);
v_i_2054_ = v___x_2066_;
v_b_2055_ = v_a_2064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2150_) == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
else
{
lean_object* v_val_2160_; lean_object* v___x_2161_; 
v_val_2160_ = lean_ctor_get(v_stx_x3f_2150_, 0);
lean_inc(v_val_2160_);
lean_dec_ref(v_stx_x3f_2150_);
v___x_2161_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2160_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2168_, lean_object* v_as_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_a_2181_; uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_b_2172_);
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; lean_object* v_a_2188_; uint8_t v___x_2189_; 
v___x_2187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2188_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
lean_inc(v_a_2188_);
v___x_2189_ = l_Lean_Syntax_isOfKind(v_a_2188_, v___x_2187_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec_ref(v___x_2190_);
v_a_2181_ = v_b_2172_;
goto v___jp_2180_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_b_2172_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___y_2202_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_unsigned_to_nat(3u);
v___x_2219_ = l_Lean_Syntax_getArg(v_a_2188_, v___x_2199_);
v___x_2220_ = l_Lean_Syntax_getArgs(v___x_2219_);
lean_dec(v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2223_ = lean_array_get_size(v___x_2220_);
v___x_2224_ = lean_nat_dec_lt(v___x_2221_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_dec_ref(v___x_2220_);
v___y_2202_ = v___x_2222_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2225_ = lean_box(v___x_2189_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2222_);
v___x_2227_ = lean_nat_dec_le(v___x_2223_, v___x_2223_);
if (v___x_2227_ == 0)
{
if (v___x_2224_ == 0)
{
lean_dec_ref(v___x_2226_);
lean_dec_ref(v___x_2220_);
v___y_2202_ = v___x_2222_;
goto v___jp_2201_;
}
else
{
size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; lean_object* v_snd_2231_; 
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = lean_usize_of_nat(v___x_2223_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2189_, v___x_2168_, v___x_2220_, v___x_2228_, v___x_2229_, v___x_2226_);
lean_dec_ref(v___x_2220_);
v_snd_2231_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2230_);
v___y_2202_ = v_snd_2231_;
goto v___jp_2201_;
}
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v_snd_2235_; 
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2223_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2189_, v___x_2168_, v___x_2220_, v___x_2232_, v___x_2233_, v___x_2226_);
lean_dec_ref(v___x_2220_);
v_snd_2235_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_snd_2235_);
lean_dec_ref(v___x_2234_);
v___y_2202_ = v_snd_2235_;
goto v___jp_2201_;
}
}
v___jp_2201_:
{
size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v_sz_2203_ = lean_array_size(v___y_2202_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2203_, v___x_2204_, v___y_2202_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_dec_ref(v___x_2206_);
v_a_2181_ = v_b_2172_;
goto v___jp_2180_;
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_b_2172_);
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v___x_2205_);
v___x_2215_ = l_Lean_Syntax_getArg(v_a_2188_, v___x_2200_);
v___x_2216_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2215_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2172_, v_a_2217_);
v_a_2181_ = v___x_2218_;
goto v___jp_2180_;
}
else
{
lean_dec_ref(v_b_2172_);
return v___x_2216_;
}
}
}
}
}
v___jp_2180_:
{
size_t v___x_2182_; size_t v___x_2183_; 
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_add(v_i_2171_, v___x_2182_);
v_i_2171_ = v___x_2183_;
v_b_2172_ = v_a_2181_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2272_ = l_Lean_NameSet_empty;
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = 0;
v___x_2275_ = 1;
v___x_2276_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2272_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*2, v___x_2275_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*2 + 1, v___x_2274_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*2 + 2, v___x_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2299_; lean_object* v_bodyInfo_2300_; lean_object* v___y_2304_; lean_object* v_bodyInfo_2305_; lean_object* v___x_2308_; lean_object* v_env_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2308_ = lean_st_ref_get(v_a_2283_);
v_env_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_ref(v_env_2309_);
lean_dec(v___x_2308_);
lean_inc(v_stx_2277_);
v___x_2310_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2310_, 0, v_env_2309_);
lean_closure_set(v___x_2310_, 1, v_stx_2277_);
v___x_2311_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2310_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_4337_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_4337_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_4337_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
if (lean_obj_tag(v_a_2312_) == 1)
{
lean_object* v_val_2316_; lean_object* v_snd_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_del_object(v___x_2314_);
lean_dec(v_stx_2277_);
v_val_2316_ = lean_ctor_get(v_a_2312_, 0);
lean_inc(v_val_2316_);
lean_dec_ref(v_a_2312_);
v_snd_2317_ = lean_ctor_get(v_val_2316_, 1);
lean_inc(v_snd_2317_);
lean_dec(v_val_2316_);
v___x_2318_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2318_, 0, lean_box(0));
lean_closure_set(v___x_2318_, 1, v_snd_2317_);
v___x_2319_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2318_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2319_);
v_stx_2277_ = v_a_2320_;
goto _start;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
v_a_2322_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2319_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2319_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___x_2512_; uint8_t v___x_2513_; uint8_t v___x_2514_; 
lean_dec(v_a_2312_);
v___x_2512_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2277_);
v___x_2513_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2512_);
v___x_2514_ = 1;
if (v___x_2513_ == 0)
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2277_);
v___x_2516_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2277_);
v___x_2518_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2277_);
v___x_2520_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2277_);
v___x_2522_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2277_);
v___x_2524_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
lean_del_object(v___x_2314_);
v___x_2525_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2277_);
v___x_2526_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2277_);
v___x_2528_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; 
v___x_2529_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2277_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2591_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2277_);
v___x_2592_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2277_);
v___x_2594_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2277_);
v___x_2596_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2277_);
v___x_2598_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2277_);
v___x_2600_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2277_);
v___x_2602_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2277_);
v___x_2604_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2277_);
v___x_2606_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2277_);
v___x_2608_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2277_);
v___x_2610_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51));
lean_inc(v_stx_2277_);
v___x_2612_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53));
lean_inc(v_stx_2277_);
v___x_2614_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55));
lean_inc(v_stx_2277_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57));
lean_inc(v_stx_2277_);
v___x_2618_ = l_Lean_Syntax_isOfKind(v_stx_2277_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v_env_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2619_ = lean_st_ref_get(v_a_2283_);
v_env_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc_ref(v_env_2620_);
lean_dec(v___x_2619_);
lean_inc_n(v_stx_2277_, 2);
v___x_2621_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2622_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2623_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2622_, v_env_2620_, v___x_2621_);
v___x_2624_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2625_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2623_, v___x_2624_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_2623_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2656_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2656_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2656_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_fst_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2654_; 
v_fst_2630_ = lean_ctor_get(v_a_2626_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_a_2626_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_a_2626_, 1);
lean_dec(v_unused_2655_);
v___x_2632_ = v_a_2626_;
v_isShared_2633_ = v_isSharedCheck_2654_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_fst_2630_);
lean_dec(v_a_2626_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2654_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
if (lean_obj_tag(v_fst_2630_) == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
lean_del_object(v___x_2628_);
v___x_2634_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2635_ = l_Lean_MessageData_ofName(v___x_2621_);
lean_inc_ref(v___x_2635_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 7);
lean_ctor_set(v___x_2632_, 1, v___x_2635_);
lean_ctor_set(v___x_2632_, 0, v___x_2634_);
v___x_2637_ = v___x_2632_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2638_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2641_ = l_Lean_indentD(v___x_2640_);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2639_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v___x_2635_);
v___x_2646_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2647_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2648_;
}
}
else
{
lean_object* v_val_2650_; lean_object* v___x_2652_; 
lean_del_object(v___x_2632_);
lean_dec(v___x_2621_);
lean_dec(v_stx_2277_);
v_val_2650_ = lean_ctor_get(v_fst_2630_, 0);
lean_inc(v_val_2650_);
lean_dec_ref(v_fst_2630_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_val_2650_);
v___x_2652_ = v___x_2628_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_val_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v___x_2621_);
lean_dec(v_stx_2277_);
v_a_2657_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2625_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2625_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___y_2669_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_unsigned_to_nat(5u);
v___x_2667_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2666_);
v___x_2678_ = lean_unsigned_to_nat(6u);
v___x_2679_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2678_);
lean_dec(v_stx_2277_);
v___x_2680_ = l_Lean_Syntax_getOptional_x3f(v___x_2679_);
lean_dec(v___x_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_box(0);
v___y_2669_ = v___x_2681_;
goto v___jp_2668_;
}
else
{
lean_object* v_val_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_val_2682_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2680_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_val_2682_);
lean_dec(v___x_2680_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_val_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
v___y_2669_ = v___x_2687_;
goto v___jp_2668_;
}
}
}
v___jp_2668_:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2667_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2670_) == 0)
{
if (lean_obj_tag(v___y_2669_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref(v___x_2670_);
v___x_2672_ = l_Lean_NameSet_empty;
v___x_2673_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2673_, 0, v___x_2665_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*2, v___x_2616_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*2 + 1, v___x_2616_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*2 + 2, v___x_2616_);
v___y_2304_ = v_a_2671_;
v_bodyInfo_2305_ = v___x_2673_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2674_; lean_object* v_val_2675_; lean_object* v___x_2676_; 
v_a_2674_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2670_);
v_val_2675_ = lean_ctor_get(v___y_2669_, 0);
lean_inc(v_val_2675_);
lean_dec_ref(v___y_2669_);
v___x_2676_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2675_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v___y_2304_ = v_a_2674_;
v_bodyInfo_2305_ = v_a_2677_;
goto v___jp_2303_;
}
else
{
lean_dec(v_a_2674_);
return v___x_2676_;
}
}
}
else
{
lean_dec(v___y_2669_);
return v___x_2670_;
}
}
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___y_2694_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2690_ = lean_unsigned_to_nat(1u);
v___x_2691_ = lean_unsigned_to_nat(5u);
v___x_2692_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2691_);
v___x_2703_ = lean_unsigned_to_nat(6u);
v___x_2704_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2703_);
lean_dec(v_stx_2277_);
v___x_2705_ = l_Lean_Syntax_getOptional_x3f(v___x_2704_);
lean_dec(v___x_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_box(0);
v___y_2694_ = v___x_2706_;
goto v___jp_2693_;
}
else
{
lean_object* v_val_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_val_2707_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2705_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_val_2707_);
lean_dec(v___x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_val_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
v___y_2694_ = v___x_2712_;
goto v___jp_2693_;
}
}
}
v___jp_2693_:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2692_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2695_) == 0)
{
if (lean_obj_tag(v___y_2694_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_NameSet_empty;
v___x_2698_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2698_, 0, v___x_2690_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*2, v___x_2614_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*2 + 1, v___x_2614_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*2 + 2, v___x_2614_);
v___y_2299_ = v_a_2696_;
v_bodyInfo_2300_ = v___x_2698_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2699_; lean_object* v_val_2700_; lean_object* v___x_2701_; 
v_a_2699_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2695_);
v_val_2700_ = lean_ctor_get(v___y_2694_, 0);
lean_inc(v_val_2700_);
lean_dec_ref(v___y_2694_);
v___x_2701_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2700_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v___y_2299_ = v_a_2699_;
v_bodyInfo_2300_ = v_a_2702_;
goto v___jp_2298_;
}
else
{
lean_dec(v_a_2699_);
return v___x_2701_;
}
}
}
else
{
lean_dec(v___y_2694_);
return v___x_2695_;
}
}
}
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_unsigned_to_nat(1u);
v___x_2930_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2716_);
v___x_2931_ = l_Lean_Syntax_isNone(v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_unsigned_to_nat(5u);
v___x_2933_ = l_Lean_Syntax_matchesNull(v___x_2930_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v_env_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2934_ = lean_st_ref_get(v_a_2283_);
v_env_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc_ref(v_env_2935_);
lean_dec(v___x_2934_);
lean_inc_n(v_stx_2277_, 2);
v___x_2936_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2937_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2938_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2937_, v_env_2935_, v___x_2936_);
v___x_2939_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2940_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2938_, v___x_2939_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2971_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2971_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2971_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_fst_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2969_; 
v_fst_2945_ = lean_ctor_get(v_a_2941_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_a_2941_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v_a_2941_, 1);
lean_dec(v_unused_2970_);
v___x_2947_ = v_a_2941_;
v_isShared_2948_ = v_isSharedCheck_2969_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_fst_2945_);
lean_dec(v_a_2941_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2969_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
if (lean_obj_tag(v_fst_2945_) == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
lean_del_object(v___x_2943_);
v___x_2949_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2950_ = l_Lean_MessageData_ofName(v___x_2936_);
lean_inc_ref(v___x_2950_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 7);
lean_ctor_set(v___x_2947_, 1, v___x_2950_);
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2953_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2956_ = l_Lean_indentD(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2954_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2950_);
v___x_2961_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2962_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2963_;
}
}
else
{
lean_object* v_val_2965_; lean_object* v___x_2967_; 
lean_del_object(v___x_2947_);
lean_dec(v___x_2936_);
lean_dec(v_stx_2277_);
v_val_2965_ = lean_ctor_get(v_fst_2945_, 0);
lean_inc(v_val_2965_);
lean_dec_ref(v_fst_2945_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v_val_2965_);
v___x_2967_ = v___x_2943_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_val_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v___x_2936_);
lean_dec(v_stx_2277_);
v_a_2972_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2940_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2940_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
v___y_2718_ = v_a_2278_;
v___y_2719_ = v_a_2279_;
v___y_2720_ = v_a_2280_;
v___y_2721_ = v_a_2281_;
v___y_2722_ = v_a_2282_;
v___y_2723_ = v_a_2283_;
goto v___jp_2717_;
}
}
else
{
lean_dec(v___x_2930_);
v___y_2718_ = v_a_2278_;
v___y_2719_ = v_a_2279_;
v___y_2720_ = v_a_2280_;
v___y_2721_ = v_a_2281_;
v___y_2722_ = v_a_2282_;
v___y_2723_ = v_a_2283_;
goto v___jp_2717_;
}
v___jp_2717_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2724_ = lean_unsigned_to_nat(4u);
v___x_2725_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2724_);
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59));
lean_inc(v___x_2725_);
v___x_2727_ = l_Lean_Syntax_isOfKind(v___x_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v_env_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_dec(v___x_2725_);
v___x_2728_ = lean_st_ref_get(v___y_2723_);
v_env_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc_ref(v_env_2729_);
lean_dec(v___x_2728_);
lean_inc_n(v_stx_2277_, 2);
v___x_2730_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2731_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2732_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2731_, v_env_2729_, v___x_2730_);
v___x_2733_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2734_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2732_, v___x_2733_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___x_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2765_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2765_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2765_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v_fst_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2763_; 
v_fst_2739_ = lean_ctor_get(v_a_2735_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_a_2735_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v_a_2735_, 1);
lean_dec(v_unused_2764_);
v___x_2741_ = v_a_2735_;
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_fst_2739_);
lean_dec(v_a_2735_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
if (lean_obj_tag(v_fst_2739_) == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
lean_del_object(v___x_2737_);
v___x_2743_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2744_ = l_Lean_MessageData_ofName(v___x_2730_);
lean_inc_ref(v___x_2744_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set_tag(v___x_2741_, 7);
lean_ctor_set(v___x_2741_, 1, v___x_2744_);
lean_ctor_set(v___x_2741_, 0, v___x_2743_);
v___x_2746_ = v___x_2741_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2747_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2750_ = l_Lean_indentD(v___x_2749_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2748_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v___x_2744_);
v___x_2755_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2756_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2757_;
}
}
else
{
lean_object* v_val_2759_; lean_object* v___x_2761_; 
lean_del_object(v___x_2741_);
lean_dec(v___x_2730_);
lean_dec(v_stx_2277_);
v_val_2759_ = lean_ctor_get(v_fst_2739_, 0);
lean_inc(v_val_2759_);
lean_dec_ref(v_fst_2739_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v_val_2759_);
v___x_2761_ = v___x_2737_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_val_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v___x_2730_);
lean_dec(v_stx_2277_);
v_a_2766_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2734_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2734_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; size_t v_sz_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2774_ = l_Lean_Syntax_getArg(v___x_2725_, v___x_2715_);
v___x_2775_ = l_Lean_Syntax_getArgs(v___x_2774_);
lean_dec(v___x_2774_);
v_sz_2776_ = lean_array_size(v___x_2775_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2776_, v___x_2777_, v___x_2775_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2779_; lean_object* v_env_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v___x_2725_);
v___x_2779_ = lean_st_ref_get(v___y_2723_);
v_env_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_ref(v_env_2780_);
lean_dec(v___x_2779_);
lean_inc_n(v_stx_2277_, 2);
v___x_2781_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2782_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2783_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2782_, v_env_2780_, v___x_2781_);
v___x_2784_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2785_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2783_, v___x_2784_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___x_2783_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2816_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2816_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2816_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_fst_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2814_; 
v_fst_2790_ = lean_ctor_get(v_a_2786_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_a_2786_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v_a_2786_, 1);
lean_dec(v_unused_2815_);
v___x_2792_ = v_a_2786_;
v_isShared_2793_ = v_isSharedCheck_2814_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_fst_2790_);
lean_dec(v_a_2786_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2814_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
if (lean_obj_tag(v_fst_2790_) == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
lean_del_object(v___x_2788_);
v___x_2794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2795_ = l_Lean_MessageData_ofName(v___x_2781_);
lean_inc_ref(v___x_2795_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 7);
lean_ctor_set(v___x_2792_, 1, v___x_2795_);
lean_ctor_set(v___x_2792_, 0, v___x_2794_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2798_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2801_ = l_Lean_indentD(v___x_2800_);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2799_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2795_);
v___x_2806_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2807_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2808_;
}
}
else
{
lean_object* v_val_2810_; lean_object* v___x_2812_; 
lean_del_object(v___x_2792_);
lean_dec(v___x_2781_);
lean_dec(v_stx_2277_);
v_val_2810_ = lean_ctor_get(v_fst_2790_, 0);
lean_inc(v_val_2810_);
lean_dec_ref(v_fst_2790_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v_val_2810_);
v___x_2812_ = v___x_2788_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_val_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v___x_2781_);
lean_dec(v_stx_2277_);
v_a_2817_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2785_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2785_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_val_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_val_2825_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_val_2825_);
lean_dec_ref(v___x_2778_);
v___x_2826_ = l_Lean_Syntax_getArg(v___x_2725_, v___x_2716_);
lean_dec(v___x_2725_);
v___x_2827_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61));
lean_inc(v___x_2826_);
v___x_2828_ = l_Lean_Syntax_isOfKind(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v_env_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec(v___x_2826_);
lean_dec(v_val_2825_);
v___x_2829_ = lean_st_ref_get(v___y_2723_);
v_env_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc_ref(v_env_2830_);
lean_dec(v___x_2829_);
lean_inc_n(v_stx_2277_, 2);
v___x_2831_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2832_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2833_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2832_, v_env_2830_, v___x_2831_);
v___x_2834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2835_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2833_, v___x_2834_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___x_2833_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2866_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2838_ = v___x_2835_;
v_isShared_2839_ = v_isSharedCheck_2866_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2835_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2866_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v_fst_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2864_; 
v_fst_2840_ = lean_ctor_get(v_a_2836_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2836_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v_a_2836_, 1);
lean_dec(v_unused_2865_);
v___x_2842_ = v_a_2836_;
v_isShared_2843_ = v_isSharedCheck_2864_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_fst_2840_);
lean_dec(v_a_2836_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2864_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
if (lean_obj_tag(v_fst_2840_) == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
lean_del_object(v___x_2838_);
v___x_2844_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2845_ = l_Lean_MessageData_ofName(v___x_2831_);
lean_inc_ref(v___x_2845_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 7);
lean_ctor_set(v___x_2842_, 1, v___x_2845_);
lean_ctor_set(v___x_2842_, 0, v___x_2844_);
v___x_2847_ = v___x_2842_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2848_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2851_ = l_Lean_indentD(v___x_2850_);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2849_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2845_);
v___x_2856_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2857_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2858_;
}
}
else
{
lean_object* v_val_2860_; lean_object* v___x_2862_; 
lean_del_object(v___x_2842_);
lean_dec(v___x_2831_);
lean_dec(v_stx_2277_);
v_val_2860_ = lean_ctor_get(v_fst_2840_, 0);
lean_inc(v_val_2860_);
lean_dec_ref(v_fst_2840_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v_val_2860_);
v___x_2862_ = v___x_2838_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_val_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v___x_2831_);
lean_dec(v_stx_2277_);
v_a_2867_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2835_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2835_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2875_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2716_);
v___x_2876_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
v___x_2877_ = l_Lean_Syntax_isOfKind(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v_env_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v___x_2826_);
lean_dec(v_val_2825_);
v___x_2878_ = lean_st_ref_get(v___y_2723_);
v_env_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc_ref(v_env_2879_);
lean_dec(v___x_2878_);
lean_inc_n(v_stx_2277_, 2);
v___x_2880_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2881_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2882_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2881_, v_env_2879_, v___x_2880_);
v___x_2883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2884_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2882_, v___x_2883_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___x_2882_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2915_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2915_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2915_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_fst_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2913_; 
v_fst_2889_ = lean_ctor_get(v_a_2885_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2885_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v_a_2885_, 1);
lean_dec(v_unused_2914_);
v___x_2891_ = v_a_2885_;
v_isShared_2892_ = v_isSharedCheck_2913_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_fst_2889_);
lean_dec(v_a_2885_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2913_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
if (lean_obj_tag(v_fst_2889_) == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_del_object(v___x_2887_);
v___x_2893_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2894_ = l_Lean_MessageData_ofName(v___x_2880_);
lean_inc_ref(v___x_2894_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 7);
lean_ctor_set(v___x_2891_, 1, v___x_2894_);
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2896_ = v___x_2891_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2897_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2900_ = l_Lean_indentD(v___x_2899_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2898_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set(v___x_2904_, 1, v___x_2894_);
v___x_2905_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2906_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2907_;
}
}
else
{
lean_object* v_val_2909_; lean_object* v___x_2911_; 
lean_del_object(v___x_2891_);
lean_dec(v___x_2880_);
lean_dec(v_stx_2277_);
v_val_2909_ = lean_ctor_get(v_fst_2889_, 0);
lean_inc(v_val_2909_);
lean_dec_ref(v_fst_2889_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_val_2909_);
v___x_2911_ = v___x_2887_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_val_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v___x_2880_);
lean_dec(v_stx_2277_);
v_a_2916_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2884_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2884_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec(v_stx_2277_);
v___x_2924_ = lean_unsigned_to_nat(3u);
v___x_2925_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2924_);
lean_dec(v___x_2826_);
v___x_2926_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2925_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; size_t v_sz_2928_; lean_object* v___x_2929_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref(v___x_2926_);
v_sz_2928_ = lean_array_size(v_val_2825_);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2825_, v_sz_2928_, v___x_2777_, v_a_2927_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v_val_2825_);
return v___x_2929_;
}
else
{
lean_dec(v_val_2825_);
return v___x_2926_;
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
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v_stx_2277_);
v___x_2980_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_dec(v_stx_2277_);
v___x_2982_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
return v___x_2983_;
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec(v_stx_2277_);
v___x_2984_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; size_t v_sz_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2986_ = lean_unsigned_to_nat(2u);
v___x_2987_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2986_);
v___x_2988_ = l_Lean_Syntax_getArgs(v___x_2987_);
lean_dec(v___x_2987_);
v_sz_2989_ = lean_array_size(v___x_2988_);
v___x_2990_ = ((size_t)0ULL);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_2989_, v___x_2990_, v___x_2988_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v___x_2992_; lean_object* v_env_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2992_ = lean_st_ref_get(v_a_2283_);
v_env_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc_ref(v_env_2993_);
lean_dec(v___x_2992_);
lean_inc_n(v_stx_2277_, 2);
v___x_2994_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2995_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2996_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2995_, v_env_2993_, v___x_2994_);
v___x_2997_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2998_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2996_, v___x_2997_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_2996_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3029_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3029_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3029_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_fst_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3027_; 
v_fst_3003_ = lean_ctor_get(v_a_2999_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v_a_2999_, 1);
lean_dec(v_unused_3028_);
v___x_3005_ = v_a_2999_;
v_isShared_3006_ = v_isSharedCheck_3027_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_fst_3003_);
lean_dec(v_a_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3027_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
if (lean_obj_tag(v_fst_3003_) == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
lean_del_object(v___x_3001_);
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3008_ = l_Lean_MessageData_ofName(v___x_2994_);
lean_inc_ref(v___x_3008_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 7);
lean_ctor_set(v___x_3005_, 1, v___x_3008_);
lean_ctor_set(v___x_3005_, 0, v___x_3007_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3011_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3014_ = l_Lean_indentD(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3012_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3008_);
v___x_3019_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3020_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3021_;
}
}
else
{
lean_object* v_val_3023_; lean_object* v___x_3025_; 
lean_del_object(v___x_3005_);
lean_dec(v___x_2994_);
lean_dec(v_stx_2277_);
v_val_3023_ = lean_ctor_get(v_fst_3003_, 0);
lean_inc(v_val_3023_);
lean_dec_ref(v_fst_3003_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v_val_3023_);
v___x_3025_ = v___x_3001_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_val_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v___x_2994_);
lean_dec(v_stx_2277_);
v_a_3030_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2998_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2998_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_val_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3172_; 
v_val_3038_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3040_ = v___x_2991_;
v_isShared_3041_ = v_isSharedCheck_3172_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_val_3038_);
lean_dec(v___x_2991_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3172_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v_finSeq_x3f_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3042_ = lean_unsigned_to_nat(1u);
v___x_3043_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3042_);
v___x_3067_ = lean_unsigned_to_nat(3u);
v___x_3068_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3067_);
v___x_3069_ = l_Lean_Syntax_isNone(v___x_3068_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
lean_inc(v___x_3068_);
v___x_3070_ = l_Lean_Syntax_matchesNull(v___x_3068_, v___x_3042_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v_env_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec(v___x_3068_);
lean_dec(v___x_3043_);
lean_del_object(v___x_3040_);
lean_dec(v_val_3038_);
v___x_3071_ = lean_st_ref_get(v_a_2283_);
v_env_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc_ref(v_env_3072_);
lean_dec(v___x_3071_);
lean_inc_n(v_stx_2277_, 2);
v___x_3073_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3074_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3075_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3074_, v_env_3072_, v___x_3073_);
v___x_3076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3077_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3075_, v___x_3076_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3075_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3108_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3108_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3108_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v_fst_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3106_; 
v_fst_3082_ = lean_ctor_get(v_a_3078_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_a_3078_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v_a_3078_, 1);
lean_dec(v_unused_3107_);
v___x_3084_ = v_a_3078_;
v_isShared_3085_ = v_isSharedCheck_3106_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_fst_3082_);
lean_dec(v_a_3078_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3106_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
if (lean_obj_tag(v_fst_3082_) == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
lean_del_object(v___x_3080_);
v___x_3086_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3087_ = l_Lean_MessageData_ofName(v___x_3073_);
lean_inc_ref(v___x_3087_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set_tag(v___x_3084_, 7);
lean_ctor_set(v___x_3084_, 1, v___x_3087_);
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3089_ = v___x_3084_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3090_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3093_ = l_Lean_indentD(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3091_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___x_3087_);
v___x_3098_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3099_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3100_;
}
}
else
{
lean_object* v_val_3102_; lean_object* v___x_3104_; 
lean_del_object(v___x_3084_);
lean_dec(v___x_3073_);
lean_dec(v_stx_2277_);
v_val_3102_ = lean_ctor_get(v_fst_3082_, 0);
lean_inc(v_val_3102_);
lean_dec_ref(v_fst_3082_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v_val_3102_);
v___x_3104_ = v___x_3080_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_val_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v___x_3073_);
lean_dec(v_stx_2277_);
v_a_3109_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3077_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3077_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = l_Lean_Syntax_getArg(v___x_3068_, v___x_3117_);
lean_dec(v___x_3068_);
v___x_3119_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65));
lean_inc(v___x_3118_);
v___x_3120_ = l_Lean_Syntax_isOfKind(v___x_3118_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v_env_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v___x_3118_);
lean_dec(v___x_3043_);
lean_del_object(v___x_3040_);
lean_dec(v_val_3038_);
v___x_3121_ = lean_st_ref_get(v_a_2283_);
v_env_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc_ref(v_env_3122_);
lean_dec(v___x_3121_);
lean_inc_n(v_stx_2277_, 2);
v___x_3123_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3124_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3125_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3124_, v_env_3122_, v___x_3123_);
v___x_3126_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3127_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3125_, v___x_3126_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3158_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3158_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3158_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_fst_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3156_; 
v_fst_3132_ = lean_ctor_get(v_a_3128_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_a_3128_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v_a_3128_, 1);
lean_dec(v_unused_3157_);
v___x_3134_ = v_a_3128_;
v_isShared_3135_ = v_isSharedCheck_3156_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_fst_3132_);
lean_dec(v_a_3128_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3156_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
if (lean_obj_tag(v_fst_3132_) == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_del_object(v___x_3130_);
v___x_3136_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3137_ = l_Lean_MessageData_ofName(v___x_3123_);
lean_inc_ref(v___x_3137_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 7);
lean_ctor_set(v___x_3134_, 1, v___x_3137_);
lean_ctor_set(v___x_3134_, 0, v___x_3136_);
v___x_3139_ = v___x_3134_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3140_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3143_ = l_Lean_indentD(v___x_3142_);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3141_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_3137_);
v___x_3148_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3149_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3150_;
}
}
else
{
lean_object* v_val_3152_; lean_object* v___x_3154_; 
lean_del_object(v___x_3134_);
lean_dec(v___x_3123_);
lean_dec(v_stx_2277_);
v_val_3152_ = lean_ctor_get(v_fst_3132_, 0);
lean_inc(v_val_3152_);
lean_dec_ref(v_fst_3132_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_val_3152_);
v___x_3154_ = v___x_3130_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_val_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v___x_3123_);
lean_dec(v_stx_2277_);
v_a_3159_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3127_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3127_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
lean_dec(v_stx_2277_);
v___x_3167_ = l_Lean_Syntax_getArg(v___x_3118_, v___x_3042_);
lean_dec(v___x_3118_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3167_);
v___x_3169_ = v___x_3040_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
v_finSeq_x3f_3045_ = v___x_3169_;
v___y_3046_ = v_a_2278_;
v___y_3047_ = v_a_2279_;
v___y_3048_ = v_a_2280_;
v___y_3049_ = v_a_2281_;
v___y_3050_ = v_a_2282_;
v___y_3051_ = v_a_2283_;
goto v___jp_3044_;
}
}
}
}
else
{
lean_object* v___x_3171_; 
lean_dec(v___x_3068_);
lean_del_object(v___x_3040_);
lean_dec(v_stx_2277_);
v___x_3171_ = lean_box(0);
v_finSeq_x3f_3045_ = v___x_3171_;
v___y_3046_ = v_a_2278_;
v___y_3047_ = v_a_2279_;
v___y_3048_ = v_a_2280_;
v___y_3049_ = v_a_2281_;
v___y_3050_ = v_a_2282_;
v___y_3051_ = v_a_2283_;
goto v___jp_3044_;
}
v___jp_3044_:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3043_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; size_t v_sz_3054_; lean_object* v___x_3055_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v_sz_3054_ = lean_array_size(v_val_3038_);
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3038_, v_sz_3054_, v___x_2990_, v_a_3053_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v_val_3038_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3066_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3056_, v_a_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
else
{
lean_dec(v_a_3056_);
return v___x_3057_;
}
}
else
{
lean_dec(v_finSeq_x3f_3045_);
return v___x_3055_;
}
}
else
{
lean_dec(v_finSeq_x3f_3045_);
lean_dec(v_val_3038_);
return v___x_3052_;
}
}
}
}
}
}
else
{
lean_object* v___x_3173_; lean_object* v___y_3175_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3173_ = lean_unsigned_to_nat(1u);
v___x_3246_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3173_);
v___x_3247_ = l_Lean_Syntax_getArgs(v___x_3246_);
lean_dec(v___x_3246_);
v___x_3248_ = lean_unsigned_to_nat(0u);
v___x_3249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3250_ = lean_array_get_size(v___x_3247_);
v___x_3251_ = lean_nat_dec_lt(v___x_3248_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_dec_ref(v___x_3247_);
v___y_3175_ = v___x_3249_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3252_ = lean_box(v___x_2604_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
lean_ctor_set(v___x_3253_, 1, v___x_3249_);
v___x_3254_ = lean_nat_dec_le(v___x_3250_, v___x_3250_);
if (v___x_3254_ == 0)
{
if (v___x_3251_ == 0)
{
lean_dec_ref(v___x_3253_);
lean_dec_ref(v___x_3247_);
v___y_3175_ = v___x_3249_;
goto v___jp_3174_;
}
else
{
size_t v___x_3255_; size_t v___x_3256_; lean_object* v___x_3257_; lean_object* v_snd_3258_; 
v___x_3255_ = ((size_t)0ULL);
v___x_3256_ = lean_usize_of_nat(v___x_3250_);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2604_, v___x_2602_, v___x_3247_, v___x_3255_, v___x_3256_, v___x_3253_);
lean_dec_ref(v___x_3247_);
v_snd_3258_ = lean_ctor_get(v___x_3257_, 1);
lean_inc(v_snd_3258_);
lean_dec_ref(v___x_3257_);
v___y_3175_ = v_snd_3258_;
goto v___jp_3174_;
}
}
else
{
size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; lean_object* v_snd_3262_; 
v___x_3259_ = ((size_t)0ULL);
v___x_3260_ = lean_usize_of_nat(v___x_3250_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2604_, v___x_2602_, v___x_3247_, v___x_3259_, v___x_3260_, v___x_3253_);
lean_dec_ref(v___x_3247_);
v_snd_3262_ = lean_ctor_get(v___x_3261_, 1);
lean_inc(v_snd_3262_);
lean_dec_ref(v___x_3261_);
v___y_3175_ = v_snd_3262_;
goto v___jp_3174_;
}
}
v___jp_3174_:
{
size_t v_sz_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
v_sz_3176_ = lean_array_size(v___y_3175_);
v___x_3177_ = ((size_t)0ULL);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3176_, v___x_3177_, v___y_3175_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3179_; lean_object* v_env_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3179_ = lean_st_ref_get(v_a_2283_);
v_env_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc_ref(v_env_3180_);
lean_dec(v___x_3179_);
lean_inc_n(v_stx_2277_, 2);
v___x_3181_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3182_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3183_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3182_, v_env_3180_, v___x_3181_);
v___x_3184_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3185_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3183_, v___x_3184_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3183_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3216_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3216_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3216_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_fst_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3214_; 
v_fst_3190_ = lean_ctor_get(v_a_3186_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_a_3186_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v_a_3186_, 1);
lean_dec(v_unused_3215_);
v___x_3192_ = v_a_3186_;
v_isShared_3193_ = v_isSharedCheck_3214_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_fst_3190_);
lean_dec(v_a_3186_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3214_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
if (lean_obj_tag(v_fst_3190_) == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_del_object(v___x_3188_);
v___x_3194_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3195_ = l_Lean_MessageData_ofName(v___x_3181_);
lean_inc_ref(v___x_3195_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set_tag(v___x_3192_, 7);
lean_ctor_set(v___x_3192_, 1, v___x_3195_);
lean_ctor_set(v___x_3192_, 0, v___x_3194_);
v___x_3197_ = v___x_3192_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3198_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3197_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3201_ = l_Lean_indentD(v___x_3200_);
v___x_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3199_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v___x_3195_);
v___x_3206_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3207_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3208_;
}
}
else
{
lean_object* v_val_3210_; lean_object* v___x_3212_; 
lean_del_object(v___x_3192_);
lean_dec(v___x_3181_);
lean_dec(v_stx_2277_);
v_val_3210_ = lean_ctor_get(v_fst_3190_, 0);
lean_inc(v_val_3210_);
lean_dec_ref(v_fst_3190_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v_val_3210_);
v___x_3212_ = v___x_3188_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_val_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v___x_3181_);
lean_dec(v_stx_2277_);
v_a_3217_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3185_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3185_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec_ref(v___x_3178_);
v___x_3225_ = lean_unsigned_to_nat(3u);
v___x_3226_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3225_);
lean_dec(v_stx_2277_);
v___x_3227_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3226_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3245_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3245_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3245_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
uint8_t v_returnsEarly_3232_; lean_object* v_reassigns_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3243_; 
v_returnsEarly_3232_ = lean_ctor_get_uint8(v_a_3228_, sizeof(void*)*2 + 2);
v_reassigns_3233_ = lean_ctor_get(v_a_3228_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_a_3228_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_a_3228_, 0);
lean_dec(v_unused_3244_);
v___x_3235_ = v_a_3228_;
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_reassigns_3233_);
lean_dec(v_a_3228_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3173_);
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_reassigns_3233_);
lean_ctor_set_uint8(v_reuseFailAlloc_3242_, sizeof(void*)*2 + 2, v_returnsEarly_3232_);
v___x_3238_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*2, v___x_2602_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*2 + 1, v___x_2602_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3238_);
v___x_3240_ = v___x_3230_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
else
{
return v___x_3227_;
}
}
}
}
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_unsigned_to_nat(3u);
v___x_3265_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3264_);
lean_dec(v_stx_2277_);
v___x_3266_ = l_Lean_NameSet_empty;
v___x_3267_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3267_, 0, v___x_3263_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*2, v___x_2600_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*2 + 1, v___x_2600_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*2 + 2, v___x_2600_);
v___x_3268_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3265_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3277_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3277_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3277_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3267_, v_a_3269_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3273_);
v___x_3275_ = v___x_3271_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
else
{
lean_dec_ref(v___x_3267_);
return v___x_3268_;
}
}
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; size_t v_sz_3281_; size_t v___x_3282_; lean_object* v___x_3283_; 
v___x_3278_ = lean_unsigned_to_nat(4u);
v___x_3279_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3278_);
v___x_3280_ = l_Lean_Syntax_getArgs(v___x_3279_);
lean_dec(v___x_3279_);
v_sz_3281_ = lean_array_size(v___x_3280_);
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3281_, v___x_3282_, v___x_3280_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v___x_3284_; lean_object* v_env_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3284_ = lean_st_ref_get(v_a_2283_);
v_env_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc_ref(v_env_3285_);
lean_dec(v___x_3284_);
lean_inc_n(v_stx_2277_, 2);
v___x_3286_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3287_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3288_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3287_, v_env_3285_, v___x_3286_);
v___x_3289_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3290_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3288_, v___x_3289_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3288_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3321_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3321_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3321_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v_fst_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3319_; 
v_fst_3295_ = lean_ctor_get(v_a_3291_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_a_3291_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v_a_3291_, 1);
lean_dec(v_unused_3320_);
v___x_3297_ = v_a_3291_;
v_isShared_3298_ = v_isSharedCheck_3319_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_fst_3295_);
lean_dec(v_a_3291_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3319_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
if (lean_obj_tag(v_fst_3295_) == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
lean_del_object(v___x_3293_);
v___x_3299_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3300_ = l_Lean_MessageData_ofName(v___x_3286_);
lean_inc_ref(v___x_3300_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 7);
lean_ctor_set(v___x_3297_, 1, v___x_3300_);
lean_ctor_set(v___x_3297_, 0, v___x_3299_);
v___x_3302_ = v___x_3297_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3303_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3306_ = l_Lean_indentD(v___x_3305_);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3304_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
lean_ctor_set(v___x_3310_, 1, v___x_3300_);
v___x_3311_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3312_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3313_;
}
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3317_; 
lean_del_object(v___x_3297_);
lean_dec(v___x_3286_);
lean_dec(v_stx_2277_);
v_val_3315_ = lean_ctor_get(v_fst_3295_, 0);
lean_inc(v_val_3315_);
lean_dec_ref(v_fst_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v_val_3315_);
v___x_3317_ = v___x_3293_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_val_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v___x_3286_);
lean_dec(v_stx_2277_);
v_a_3322_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3290_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3290_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v_val_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3417_; 
v_val_3330_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3332_ = v___x_3283_;
v_isShared_3333_ = v_isSharedCheck_3417_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_val_3330_);
lean_dec(v___x_3283_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3417_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v_elseSeq_x3f_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3334_ = lean_unsigned_to_nat(3u);
v___x_3335_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3334_);
v___x_3360_ = lean_unsigned_to_nat(5u);
v___x_3361_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3360_);
v___x_3362_ = l_Lean_Syntax_isNone(v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3361_);
v___x_3364_ = l_Lean_Syntax_matchesNull(v___x_3361_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v_env_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
lean_dec(v___x_3361_);
lean_dec(v___x_3335_);
lean_del_object(v___x_3332_);
lean_dec(v_val_3330_);
v___x_3365_ = lean_st_ref_get(v_a_2283_);
v_env_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc_ref(v_env_3366_);
lean_dec(v___x_3365_);
lean_inc_n(v_stx_2277_, 2);
v___x_3367_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3368_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3369_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3368_, v_env_3366_, v___x_3367_);
v___x_3370_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3371_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3369_, v___x_3370_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3369_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3402_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3402_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3402_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_fst_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3400_; 
v_fst_3376_ = lean_ctor_get(v_a_3372_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v_a_3372_, 1);
lean_dec(v_unused_3401_);
v___x_3378_ = v_a_3372_;
v_isShared_3379_ = v_isSharedCheck_3400_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_fst_3376_);
lean_dec(v_a_3372_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3400_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
if (lean_obj_tag(v_fst_3376_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_del_object(v___x_3374_);
v___x_3380_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3381_ = l_Lean_MessageData_ofName(v___x_3367_);
lean_inc_ref(v___x_3381_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 7);
lean_ctor_set(v___x_3378_, 1, v___x_3381_);
lean_ctor_set(v___x_3378_, 0, v___x_3380_);
v___x_3383_ = v___x_3378_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3387_ = l_Lean_indentD(v___x_3386_);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3385_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___x_3381_);
v___x_3392_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3393_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3394_;
}
}
else
{
lean_object* v_val_3396_; lean_object* v___x_3398_; 
lean_del_object(v___x_3378_);
lean_dec(v___x_3367_);
lean_dec(v_stx_2277_);
v_val_3396_ = lean_ctor_get(v_fst_3376_, 0);
lean_inc(v_val_3396_);
lean_dec_ref(v_fst_3376_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v_val_3396_);
v___x_3398_ = v___x_3374_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_val_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v___x_3367_);
lean_dec(v_stx_2277_);
v_a_3403_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3371_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3371_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
lean_dec(v_stx_2277_);
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = l_Lean_Syntax_getArg(v___x_3361_, v___x_3411_);
lean_dec(v___x_3361_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3412_);
v___x_3414_ = v___x_3332_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
v_elseSeq_x3f_3337_ = v___x_3414_;
v___y_3338_ = v_a_2278_;
v___y_3339_ = v_a_2279_;
v___y_3340_ = v_a_2280_;
v___y_3341_ = v_a_2281_;
v___y_3342_ = v_a_2282_;
v___y_3343_ = v_a_2283_;
goto v___jp_3336_;
}
}
}
else
{
lean_object* v___x_3416_; 
lean_dec(v___x_3361_);
lean_del_object(v___x_3332_);
lean_dec(v_stx_2277_);
v___x_3416_ = lean_box(0);
v_elseSeq_x3f_3337_ = v___x_3416_;
v___y_3338_ = v_a_2278_;
v___y_3339_ = v_a_2279_;
v___y_3340_ = v_a_2280_;
v___y_3341_ = v_a_2281_;
v___y_3342_ = v_a_2282_;
v___y_3343_ = v_a_2283_;
goto v___jp_3336_;
}
v___jp_3336_:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; size_t v_sz_3347_; lean_object* v___x_3348_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = l_Array_reverse___redArg(v_val_3330_);
v_sz_3347_ = lean_array_size(v___x_3346_);
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3346_, v_sz_3347_, v___x_3282_, v_a_3345_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec_ref(v___x_3346_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3335_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3359_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3359_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3359_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3351_, v_a_3349_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3355_);
v___x_3357_ = v___x_3353_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_dec(v_a_3349_);
return v___x_3350_;
}
}
else
{
lean_dec(v___x_3335_);
return v___x_3348_;
}
}
else
{
lean_dec(v___x_3335_);
lean_dec(v_val_3330_);
return v___x_3344_;
}
}
}
}
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3418_ = lean_unsigned_to_nat(0u);
v___x_3419_ = lean_unsigned_to_nat(1u);
v___x_3590_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3419_);
v___x_3591_ = l_Lean_Syntax_isNone(v___x_3590_);
if (v___x_3591_ == 0)
{
uint8_t v___x_3592_; 
lean_inc(v___x_3590_);
v___x_3592_ = l_Lean_Syntax_matchesNull(v___x_3590_, v___x_3419_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v_env_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec(v___x_3590_);
v___x_3593_ = lean_st_ref_get(v_a_2283_);
v_env_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_ref(v_env_3594_);
lean_dec(v___x_3593_);
lean_inc_n(v_stx_2277_, 2);
v___x_3595_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3596_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3597_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3596_, v_env_3594_, v___x_3595_);
v___x_3598_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3599_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3597_, v___x_3598_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3597_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3630_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3630_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3630_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v_fst_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3628_; 
v_fst_3604_ = lean_ctor_get(v_a_3600_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_a_3600_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v_a_3600_, 1);
lean_dec(v_unused_3629_);
v___x_3606_ = v_a_3600_;
v_isShared_3607_ = v_isSharedCheck_3628_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_fst_3604_);
lean_dec(v_a_3600_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3628_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
if (lean_obj_tag(v_fst_3604_) == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_del_object(v___x_3602_);
v___x_3608_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3609_ = l_Lean_MessageData_ofName(v___x_3595_);
lean_inc_ref(v___x_3609_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set_tag(v___x_3606_, 7);
lean_ctor_set(v___x_3606_, 1, v___x_3609_);
lean_ctor_set(v___x_3606_, 0, v___x_3608_);
v___x_3611_ = v___x_3606_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3612_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3615_ = l_Lean_indentD(v___x_3614_);
v___x_3616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3613_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
lean_ctor_set(v___x_3619_, 1, v___x_3609_);
v___x_3620_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3621_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3622_;
}
}
else
{
lean_object* v_val_3624_; lean_object* v___x_3626_; 
lean_del_object(v___x_3606_);
lean_dec(v___x_3595_);
lean_dec(v_stx_2277_);
v_val_3624_ = lean_ctor_get(v_fst_3604_, 0);
lean_inc(v_val_3624_);
lean_dec_ref(v_fst_3604_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v_val_3624_);
v___x_3626_ = v___x_3602_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_val_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v___x_3595_);
lean_dec(v_stx_2277_);
v_a_3631_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3599_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3599_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = l_Lean_Syntax_getArg(v___x_3590_, v___x_3418_);
lean_dec(v___x_3590_);
v___x_3640_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69));
v___x_3641_ = l_Lean_Syntax_isOfKind(v___x_3639_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v_env_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3642_ = lean_st_ref_get(v_a_2283_);
v_env_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc_ref(v_env_3643_);
lean_dec(v___x_3642_);
lean_inc_n(v_stx_2277_, 2);
v___x_3644_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3645_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3646_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3645_, v_env_3643_, v___x_3644_);
v___x_3647_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3648_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3646_, v___x_3647_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3646_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3679_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3679_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3679_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_fst_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3677_; 
v_fst_3653_ = lean_ctor_get(v_a_3649_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_a_3649_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v_a_3649_, 1);
lean_dec(v_unused_3678_);
v___x_3655_ = v_a_3649_;
v_isShared_3656_ = v_isSharedCheck_3677_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_fst_3653_);
lean_dec(v_a_3649_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3677_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
if (lean_obj_tag(v_fst_3653_) == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_del_object(v___x_3651_);
v___x_3657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3658_ = l_Lean_MessageData_ofName(v___x_3644_);
lean_inc_ref(v___x_3658_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 7);
lean_ctor_set(v___x_3655_, 1, v___x_3658_);
lean_ctor_set(v___x_3655_, 0, v___x_3657_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3661_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3664_ = l_Lean_indentD(v___x_3663_);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3662_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3665_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
lean_ctor_set(v___x_3668_, 1, v___x_3658_);
v___x_3669_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3670_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3671_;
}
}
else
{
lean_object* v_val_3673_; lean_object* v___x_3675_; 
lean_del_object(v___x_3655_);
lean_dec(v___x_3644_);
lean_dec(v_stx_2277_);
v_val_3673_ = lean_ctor_get(v_fst_3653_, 0);
lean_inc(v_val_3673_);
lean_dec_ref(v_fst_3653_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v_val_3673_);
v___x_3675_ = v___x_3651_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_val_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec(v___x_3644_);
lean_dec(v_stx_2277_);
v_a_3680_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3648_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3648_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
v___y_3485_ = v_a_2278_;
v___y_3486_ = v_a_2279_;
v___y_3487_ = v_a_2280_;
v___y_3488_ = v_a_2281_;
v___y_3489_ = v_a_2282_;
v___y_3490_ = v_a_2283_;
goto v___jp_3484_;
}
}
}
else
{
lean_dec(v___x_3590_);
v___y_3485_ = v_a_2278_;
v___y_3486_ = v_a_2279_;
v___y_3487_ = v_a_2280_;
v___y_3488_ = v_a_2281_;
v___y_3489_ = v_a_2282_;
v___y_3490_ = v_a_2283_;
goto v___jp_3484_;
}
v___jp_3420_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3427_ = lean_unsigned_to_nat(6u);
v___x_3428_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3427_);
v___x_3429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3428_);
v___x_3430_ = l_Lean_Syntax_isOfKind(v___x_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v_env_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec(v___x_3428_);
v___x_3431_ = lean_st_ref_get(v___y_3426_);
v_env_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc_ref(v_env_3432_);
lean_dec(v___x_3431_);
lean_inc_n(v_stx_2277_, 2);
v___x_3433_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3434_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3435_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3434_, v_env_3432_, v___x_3433_);
v___x_3436_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3437_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3435_, v___x_3436_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___x_3435_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3468_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3468_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3468_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_fst_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3466_; 
v_fst_3442_ = lean_ctor_get(v_a_3438_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_a_3438_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v_a_3438_, 1);
lean_dec(v_unused_3467_);
v___x_3444_ = v_a_3438_;
v_isShared_3445_ = v_isSharedCheck_3466_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_fst_3442_);
lean_dec(v_a_3438_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3466_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
if (lean_obj_tag(v_fst_3442_) == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_del_object(v___x_3440_);
v___x_3446_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3447_ = l_Lean_MessageData_ofName(v___x_3433_);
lean_inc_ref(v___x_3447_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 7);
lean_ctor_set(v___x_3444_, 1, v___x_3447_);
lean_ctor_set(v___x_3444_, 0, v___x_3446_);
v___x_3449_ = v___x_3444_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3450_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3453_ = l_Lean_indentD(v___x_3452_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3451_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3447_);
v___x_3458_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3459_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
return v___x_3460_;
}
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; 
lean_del_object(v___x_3444_);
lean_dec(v___x_3433_);
lean_dec(v_stx_2277_);
v_val_3462_ = lean_ctor_get(v_fst_3442_, 0);
lean_inc(v_val_3462_);
lean_dec_ref(v_fst_3442_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_val_3462_);
v___x_3464_ = v___x_3440_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_val_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v___x_3433_);
lean_dec(v_stx_2277_);
v_a_3469_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3437_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3437_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; size_t v_sz_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v_stx_2277_);
v___x_3477_ = l_Lean_Syntax_getArg(v___x_3428_, v___x_3418_);
lean_dec(v___x_3428_);
v___x_3478_ = l_Lean_Syntax_getArgs(v___x_3477_);
lean_dec(v___x_3477_);
v___x_3479_ = l_Lean_NameSet_empty;
v___x_3480_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3480_, 0, v___x_3419_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*2, v___x_2596_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*2 + 1, v___x_2596_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*2 + 2, v___x_2596_);
v_sz_3481_ = lean_array_size(v___x_3478_);
v___x_3482_ = ((size_t)0ULL);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2596_, v___x_3478_, v_sz_3481_, v___x_3482_, v___x_3480_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___x_3478_);
return v___x_3483_;
}
}
v___jp_3484_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3491_ = lean_unsigned_to_nat(2u);
v___x_3492_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3491_);
v___x_3493_ = l_Lean_Syntax_isNone(v___x_3492_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
lean_inc(v___x_3492_);
v___x_3494_ = l_Lean_Syntax_matchesNull(v___x_3492_, v___x_3419_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v_env_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec(v___x_3492_);
v___x_3495_ = lean_st_ref_get(v___y_3490_);
v_env_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_env_3496_);
lean_dec(v___x_3495_);
lean_inc_n(v_stx_2277_, 2);
v___x_3497_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3498_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3499_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3498_, v_env_3496_, v___x_3497_);
v___x_3500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3501_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3499_, v___x_3500_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___x_3499_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3532_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3532_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3532_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_fst_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3530_; 
v_fst_3506_ = lean_ctor_get(v_a_3502_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v_a_3502_, 1);
lean_dec(v_unused_3531_);
v___x_3508_ = v_a_3502_;
v_isShared_3509_ = v_isSharedCheck_3530_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_fst_3506_);
lean_dec(v_a_3502_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3530_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
if (lean_obj_tag(v_fst_3506_) == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_del_object(v___x_3504_);
v___x_3510_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3511_ = l_Lean_MessageData_ofName(v___x_3497_);
lean_inc_ref(v___x_3511_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 7);
lean_ctor_set(v___x_3508_, 1, v___x_3511_);
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3513_ = v___x_3508_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3514_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3513_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3517_ = l_Lean_indentD(v___x_3516_);
v___x_3518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3515_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___x_3511_);
v___x_3522_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3523_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
return v___x_3524_;
}
}
else
{
lean_object* v_val_3526_; lean_object* v___x_3528_; 
lean_del_object(v___x_3508_);
lean_dec(v___x_3497_);
lean_dec(v_stx_2277_);
v_val_3526_ = lean_ctor_get(v_fst_3506_, 0);
lean_inc(v_val_3526_);
lean_dec_ref(v_fst_3506_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v_val_3526_);
v___x_3528_ = v___x_3504_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_val_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v___x_3497_);
lean_dec(v_stx_2277_);
v_a_3533_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3501_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3501_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = l_Lean_Syntax_getArg(v___x_3492_, v___x_3418_);
lean_dec(v___x_3492_);
v___x_3542_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67));
v___x_3543_ = l_Lean_Syntax_isOfKind(v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v_env_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3544_ = lean_st_ref_get(v___y_3490_);
v_env_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc_ref(v_env_3545_);
lean_dec(v___x_3544_);
lean_inc_n(v_stx_2277_, 2);
v___x_3546_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3547_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3548_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3547_, v_env_3545_, v___x_3546_);
v___x_3549_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3550_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3548_, v___x_3549_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___x_3548_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3581_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3581_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3581_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_fst_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3579_; 
v_fst_3555_ = lean_ctor_get(v_a_3551_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v_a_3551_, 1);
lean_dec(v_unused_3580_);
v___x_3557_ = v_a_3551_;
v_isShared_3558_ = v_isSharedCheck_3579_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_fst_3555_);
lean_dec(v_a_3551_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3579_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
if (lean_obj_tag(v_fst_3555_) == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
lean_del_object(v___x_3553_);
v___x_3559_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3560_ = l_Lean_MessageData_ofName(v___x_3546_);
lean_inc_ref(v___x_3560_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 7);
lean_ctor_set(v___x_3557_, 1, v___x_3560_);
lean_ctor_set(v___x_3557_, 0, v___x_3559_);
v___x_3562_ = v___x_3557_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3563_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3566_ = l_Lean_indentD(v___x_3565_);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3564_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
lean_ctor_set(v___x_3570_, 1, v___x_3560_);
v___x_3571_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3572_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
return v___x_3573_;
}
}
else
{
lean_object* v_val_3575_; lean_object* v___x_3577_; 
lean_del_object(v___x_3557_);
lean_dec(v___x_3546_);
lean_dec(v_stx_2277_);
v_val_3575_ = lean_ctor_get(v_fst_3555_, 0);
lean_inc(v_val_3575_);
lean_dec_ref(v_fst_3555_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v_val_3575_);
v___x_3577_ = v___x_3553_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_val_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v___x_3546_);
lean_dec(v_stx_2277_);
v_a_3582_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3550_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3550_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3486_;
v___y_3423_ = v___y_3487_;
v___y_3424_ = v___y_3488_;
v___y_3425_ = v___y_3489_;
v___y_3426_ = v___y_3490_;
goto v___jp_3420_;
}
}
}
else
{
lean_dec(v___x_3492_);
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3486_;
v___y_3423_ = v___y_3487_;
v___y_3424_ = v___y_3488_;
v___y_3425_ = v___y_3489_;
v___y_3426_ = v___y_3490_;
goto v___jp_3420_;
}
}
}
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3688_);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3689_);
v___x_3691_ = l_Lean_Syntax_isOfKind(v___x_3689_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3692_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3689_);
v___x_3693_ = l_Lean_Syntax_isOfKind(v___x_3689_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; lean_object* v_env_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_dec(v___x_3689_);
v___x_3694_ = lean_st_ref_get(v_a_2283_);
v_env_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc_ref(v_env_3695_);
lean_dec(v___x_3694_);
lean_inc_n(v_stx_2277_, 2);
v___x_3696_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3697_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3698_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3697_, v_env_3695_, v___x_3696_);
v___x_3699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3700_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3698_, v___x_3699_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3698_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3731_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3731_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3731_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v_fst_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3729_; 
v_fst_3705_ = lean_ctor_get(v_a_3701_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_a_3701_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_a_3701_, 1);
lean_dec(v_unused_3730_);
v___x_3707_ = v_a_3701_;
v_isShared_3708_ = v_isSharedCheck_3729_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_fst_3705_);
lean_dec(v_a_3701_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3729_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
if (lean_obj_tag(v_fst_3705_) == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
lean_del_object(v___x_3703_);
v___x_3709_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3710_ = l_Lean_MessageData_ofName(v___x_3696_);
lean_inc_ref(v___x_3710_);
if (v_isShared_3708_ == 0)
{
lean_ctor_set_tag(v___x_3707_, 7);
lean_ctor_set(v___x_3707_, 1, v___x_3710_);
lean_ctor_set(v___x_3707_, 0, v___x_3709_);
v___x_3712_ = v___x_3707_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3713_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3716_ = l_Lean_indentD(v___x_3715_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3714_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v___x_3710_);
v___x_3721_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3722_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3723_;
}
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3727_; 
lean_del_object(v___x_3707_);
lean_dec(v___x_3696_);
lean_dec(v_stx_2277_);
v_val_3725_ = lean_ctor_get(v_fst_3705_, 0);
lean_inc(v_val_3725_);
lean_dec_ref(v_fst_3705_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v_val_3725_);
v___x_3727_ = v___x_3703_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_val_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v___x_3696_);
lean_dec(v_stx_2277_);
v_a_3732_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3700_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3700_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v___x_3740_; 
lean_dec(v_stx_2277_);
v___x_3740_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2514_, v___x_3689_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3740_;
}
}
else
{
lean_object* v___x_3741_; 
lean_dec(v_stx_2277_);
v___x_3741_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2514_, v___x_3689_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3741_;
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3742_ = lean_unsigned_to_nat(0u);
v___x_3743_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3742_);
v___x_3744_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71));
lean_inc(v___x_3743_);
v___x_3745_ = l_Lean_Syntax_isOfKind(v___x_3743_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; uint8_t v___x_3747_; 
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73));
lean_inc(v___x_3743_);
v___x_3747_ = l_Lean_Syntax_isOfKind(v___x_3743_, v___x_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v_env_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec(v___x_3743_);
v___x_3748_ = lean_st_ref_get(v_a_2283_);
v_env_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc_ref(v_env_3749_);
lean_dec(v___x_3748_);
lean_inc_n(v_stx_2277_, 2);
v___x_3750_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3751_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3752_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3751_, v_env_3749_, v___x_3750_);
v___x_3753_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3754_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3752_, v___x_3753_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3752_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3785_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3785_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3785_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v_fst_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3783_; 
v_fst_3759_ = lean_ctor_get(v_a_3755_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_a_3755_);
if (v_isSharedCheck_3783_ == 0)
{
lean_object* v_unused_3784_; 
v_unused_3784_ = lean_ctor_get(v_a_3755_, 1);
lean_dec(v_unused_3784_);
v___x_3761_ = v_a_3755_;
v_isShared_3762_ = v_isSharedCheck_3783_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_fst_3759_);
lean_dec(v_a_3755_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3783_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
if (lean_obj_tag(v_fst_3759_) == 0)
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_del_object(v___x_3757_);
v___x_3763_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3764_ = l_Lean_MessageData_ofName(v___x_3750_);
lean_inc_ref(v___x_3764_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 7);
lean_ctor_set(v___x_3761_, 1, v___x_3764_);
lean_ctor_set(v___x_3761_, 0, v___x_3763_);
v___x_3766_ = v___x_3761_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3767_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3770_ = l_Lean_indentD(v___x_3769_);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3768_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
lean_ctor_set(v___x_3774_, 1, v___x_3764_);
v___x_3775_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3774_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3776_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3777_;
}
}
else
{
lean_object* v_val_3779_; lean_object* v___x_3781_; 
lean_del_object(v___x_3761_);
lean_dec(v___x_3750_);
lean_dec(v_stx_2277_);
v_val_3779_ = lean_ctor_get(v_fst_3759_, 0);
lean_inc(v_val_3779_);
lean_dec_ref(v_fst_3759_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v_val_3779_);
v___x_3781_ = v___x_3757_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_val_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v___x_3750_);
lean_dec(v_stx_2277_);
v_a_3786_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3754_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3754_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v___x_3794_; 
lean_dec(v_stx_2277_);
v___x_3794_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3743_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3743_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = lean_box(0);
v___x_3797_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3795_, v___x_3796_, v___x_3796_, v___x_3796_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3797_;
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_a_3798_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3794_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3794_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
else
{
lean_object* v___x_3806_; 
lean_dec(v_stx_2277_);
v___x_3806_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3743_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3743_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = lean_box(0);
v___x_3809_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3807_, v___x_3808_, v___x_3808_, v___x_3808_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3809_;
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
v_a_3810_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3806_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3806_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
v___x_3818_ = lean_unsigned_to_nat(1u);
v___x_3819_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3818_);
v___x_3820_ = l_Lean_Syntax_isNone(v___x_3819_);
if (v___x_3820_ == 0)
{
uint8_t v___x_3821_; 
v___x_3821_ = l_Lean_Syntax_matchesNull(v___x_3819_, v___x_3818_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; lean_object* v_env_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3822_ = lean_st_ref_get(v_a_2283_);
v_env_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc_ref(v_env_3823_);
lean_dec(v___x_3822_);
lean_inc_n(v_stx_2277_, 2);
v___x_3824_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3825_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3826_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3825_, v_env_3823_, v___x_3824_);
v___x_3827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3828_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3826_, v___x_3827_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3826_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3859_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3859_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3859_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_fst_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3857_; 
v_fst_3833_ = lean_ctor_get(v_a_3829_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_a_3829_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v_a_3829_, 1);
lean_dec(v_unused_3858_);
v___x_3835_ = v_a_3829_;
v_isShared_3836_ = v_isSharedCheck_3857_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_fst_3833_);
lean_dec(v_a_3829_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3857_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
if (lean_obj_tag(v_fst_3833_) == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
lean_del_object(v___x_3831_);
v___x_3837_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3838_ = l_Lean_MessageData_ofName(v___x_3824_);
lean_inc_ref(v___x_3838_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 7);
lean_ctor_set(v___x_3835_, 1, v___x_3838_);
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3840_ = v___x_3835_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3841_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3844_ = l_Lean_indentD(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3842_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v___x_3838_);
v___x_3849_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3850_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3851_;
}
}
else
{
lean_object* v_val_3853_; lean_object* v___x_3855_; 
lean_del_object(v___x_3835_);
lean_dec(v___x_3824_);
lean_dec(v_stx_2277_);
v_val_3853_ = lean_ctor_get(v_fst_3833_, 0);
lean_inc(v_val_3853_);
lean_dec_ref(v_fst_3833_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v_val_3853_);
v___x_3855_ = v___x_3831_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_val_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v___x_3824_);
lean_dec(v_stx_2277_);
v_a_3860_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3828_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3828_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
v___y_2532_ = v_a_2278_;
v___y_2533_ = v_a_2279_;
v___y_2534_ = v_a_2280_;
v___y_2535_ = v_a_2281_;
v___y_2536_ = v_a_2282_;
v___y_2537_ = v_a_2283_;
goto v___jp_2531_;
}
}
else
{
lean_dec(v___x_3819_);
v___y_2532_ = v_a_2278_;
v___y_2533_ = v_a_2279_;
v___y_2534_ = v_a_2280_;
v___y_2535_ = v_a_2281_;
v___y_2536_ = v_a_2282_;
v___y_2537_ = v_a_2283_;
goto v___jp_2531_;
}
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3868_);
v___x_3870_ = l_Lean_Syntax_isNone(v___x_3869_);
if (v___x_3870_ == 0)
{
uint8_t v___x_3871_; 
v___x_3871_ = l_Lean_Syntax_matchesNull(v___x_3869_, v___x_3868_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v_env_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3872_ = lean_st_ref_get(v_a_2283_);
v_env_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc_ref(v_env_3873_);
lean_dec(v___x_3872_);
lean_inc_n(v_stx_2277_, 2);
v___x_3874_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3875_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3876_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3875_, v_env_3873_, v___x_3874_);
v___x_3877_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3878_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3876_, v___x_3877_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3876_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3909_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3909_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3909_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v_fst_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3907_; 
v_fst_3883_ = lean_ctor_get(v_a_3879_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_a_3879_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v_a_3879_, 1);
lean_dec(v_unused_3908_);
v___x_3885_ = v_a_3879_;
v_isShared_3886_ = v_isSharedCheck_3907_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_fst_3883_);
lean_dec(v_a_3879_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3907_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
if (lean_obj_tag(v_fst_3883_) == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
lean_del_object(v___x_3881_);
v___x_3887_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3888_ = l_Lean_MessageData_ofName(v___x_3874_);
lean_inc_ref(v___x_3888_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set_tag(v___x_3885_, 7);
lean_ctor_set(v___x_3885_, 1, v___x_3888_);
lean_ctor_set(v___x_3885_, 0, v___x_3887_);
v___x_3890_ = v___x_3885_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3891_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3894_ = l_Lean_indentD(v___x_3893_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3892_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v___x_3888_);
v___x_3899_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3898_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
v___x_3901_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3900_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3901_;
}
}
else
{
lean_object* v_val_3903_; lean_object* v___x_3905_; 
lean_del_object(v___x_3885_);
lean_dec(v___x_3874_);
lean_dec(v_stx_2277_);
v_val_3903_ = lean_ctor_get(v_fst_3883_, 0);
lean_inc(v_val_3903_);
lean_dec_ref(v_fst_3883_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v_val_3903_);
v___x_3905_ = v___x_3881_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_val_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v___x_3874_);
lean_dec(v_stx_2277_);
v_a_3910_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3878_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3878_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
v___y_2331_ = v_a_2278_;
v___y_2332_ = v_a_2279_;
v___y_2333_ = v_a_2280_;
v___y_2334_ = v_a_2281_;
v___y_2335_ = v_a_2282_;
v___y_2336_ = v_a_2283_;
goto v___jp_2330_;
}
}
else
{
lean_dec(v___x_3869_);
v___y_2331_ = v_a_2278_;
v___y_2332_ = v_a_2279_;
v___y_2333_ = v_a_2280_;
v___y_2334_ = v_a_2281_;
v___y_2335_ = v_a_2282_;
v___y_2336_ = v_a_2283_;
goto v___jp_2330_;
}
}
v___jp_2531_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2538_ = lean_unsigned_to_nat(2u);
v___x_2539_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2538_);
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2541_ = l_Lean_Syntax_isOfKind(v___x_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v_env_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2542_ = lean_st_ref_get(v___y_2537_);
v_env_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_ref(v_env_2543_);
lean_dec(v___x_2542_);
lean_inc_n(v_stx_2277_, 2);
v___x_2544_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2545_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2546_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2545_, v_env_2543_, v___x_2544_);
v___x_2547_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2548_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2546_, v___x_2547_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___x_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2579_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2579_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2579_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_fst_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2577_; 
v_fst_2553_ = lean_ctor_get(v_a_2549_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_a_2549_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v_a_2549_, 1);
lean_dec(v_unused_2578_);
v___x_2555_ = v_a_2549_;
v_isShared_2556_ = v_isSharedCheck_2577_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_fst_2553_);
lean_dec(v_a_2549_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2577_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
if (lean_obj_tag(v_fst_2553_) == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_del_object(v___x_2551_);
v___x_2557_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2558_ = l_Lean_MessageData_ofName(v___x_2544_);
lean_inc_ref(v___x_2558_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 7);
lean_ctor_set(v___x_2555_, 1, v___x_2558_);
lean_ctor_set(v___x_2555_, 0, v___x_2557_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2561_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2564_ = l_Lean_indentD(v___x_2563_);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2562_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2558_);
v___x_2569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2570_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2571_;
}
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2575_; 
lean_del_object(v___x_2555_);
lean_dec(v___x_2544_);
lean_dec(v_stx_2277_);
v_val_2573_ = lean_ctor_get(v_fst_2553_, 0);
lean_inc(v_val_2573_);
lean_dec_ref(v_fst_2553_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_val_2573_);
v___x_2575_ = v___x_2551_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_val_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v___x_2544_);
lean_dec(v_stx_2277_);
v_a_2580_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2548_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2548_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_unsigned_to_nat(3u);
v___x_2589_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2588_);
lean_dec(v_stx_2277_);
v___x_2590_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2530_, v___x_2589_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2590_;
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3918_);
v___x_3920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3921_ = l_Lean_Syntax_isOfKind(v___x_3919_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v_env_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3922_ = lean_st_ref_get(v_a_2283_);
v_env_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc_ref(v_env_3923_);
lean_dec(v___x_3922_);
lean_inc_n(v_stx_2277_, 2);
v___x_3924_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3925_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3926_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3925_, v_env_3923_, v___x_3924_);
v___x_3927_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3928_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3926_, v___x_3927_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3926_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3959_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3959_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3959_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v_fst_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3957_; 
v_fst_3933_ = lean_ctor_get(v_a_3929_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_a_3929_);
if (v_isSharedCheck_3957_ == 0)
{
lean_object* v_unused_3958_; 
v_unused_3958_ = lean_ctor_get(v_a_3929_, 1);
lean_dec(v_unused_3958_);
v___x_3935_ = v_a_3929_;
v_isShared_3936_ = v_isSharedCheck_3957_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_fst_3933_);
lean_dec(v_a_3929_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3957_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
if (lean_obj_tag(v_fst_3933_) == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3940_; 
lean_del_object(v___x_3931_);
v___x_3937_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3938_ = l_Lean_MessageData_ofName(v___x_3924_);
lean_inc_ref(v___x_3938_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set_tag(v___x_3935_, 7);
lean_ctor_set(v___x_3935_, 1, v___x_3938_);
lean_ctor_set(v___x_3935_, 0, v___x_3937_);
v___x_3940_ = v___x_3935_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3941_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3944_ = l_Lean_indentD(v___x_3943_);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3942_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
lean_ctor_set(v___x_3948_, 1, v___x_3938_);
v___x_3949_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3950_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_3951_;
}
}
else
{
lean_object* v_val_3953_; lean_object* v___x_3955_; 
lean_del_object(v___x_3935_);
lean_dec(v___x_3924_);
lean_dec(v_stx_2277_);
v_val_3953_ = lean_ctor_get(v_fst_3933_, 0);
lean_inc(v_val_3953_);
lean_dec_ref(v_fst_3933_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v_val_3953_);
v___x_3955_ = v___x_3931_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_val_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v___x_3924_);
lean_dec(v_stx_2277_);
v_a_3960_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3928_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3928_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_3968_);
v___x_3970_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75));
lean_inc(v___x_3969_);
v___x_3971_ = l_Lean_Syntax_isOfKind(v___x_3969_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v_env_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec(v___x_3969_);
v___x_3972_ = lean_st_ref_get(v_a_2283_);
v_env_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc_ref(v_env_3973_);
lean_dec(v___x_3972_);
lean_inc_n(v_stx_2277_, 2);
v___x_3974_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_3975_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3976_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3975_, v_env_3973_, v___x_3974_);
v___x_3977_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3978_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_3976_, v___x_3977_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_3976_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4009_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_4009_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4009_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v_fst_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4007_; 
v_fst_3983_ = lean_ctor_get(v_a_3979_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_a_3979_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; 
v_unused_4008_ = lean_ctor_get(v_a_3979_, 1);
lean_dec(v_unused_4008_);
v___x_3985_ = v_a_3979_;
v_isShared_3986_ = v_isSharedCheck_4007_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_fst_3983_);
lean_dec(v_a_3979_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4007_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
if (lean_obj_tag(v_fst_3983_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
lean_del_object(v___x_3981_);
v___x_3987_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3988_ = l_Lean_MessageData_ofName(v___x_3974_);
lean_inc_ref(v___x_3988_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set_tag(v___x_3985_, 7);
lean_ctor_set(v___x_3985_, 1, v___x_3988_);
lean_ctor_set(v___x_3985_, 0, v___x_3987_);
v___x_3990_ = v___x_3985_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3991_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_3994_ = l_Lean_indentD(v___x_3993_);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3992_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v___x_3988_);
v___x_3999_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3998_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4000_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4001_;
}
}
else
{
lean_object* v_val_4003_; lean_object* v___x_4005_; 
lean_del_object(v___x_3985_);
lean_dec(v___x_3974_);
lean_dec(v_stx_2277_);
v_val_4003_ = lean_ctor_get(v_fst_3983_, 0);
lean_inc(v_val_4003_);
lean_dec_ref(v_fst_3983_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v_val_4003_);
v___x_4005_ = v___x_3981_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_val_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v___x_3974_);
lean_dec(v_stx_2277_);
v_a_4010_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3978_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3978_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
else
{
lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4018_ = l_Lean_Syntax_getArg(v___x_3969_, v___x_3918_);
lean_dec(v___x_3969_);
lean_inc(v___x_4018_);
v___x_4019_ = l_Lean_Syntax_matchesNull(v___x_4018_, v___x_3968_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v_env_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec(v___x_4018_);
v___x_4020_ = lean_st_ref_get(v_a_2283_);
v_env_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc_ref(v_env_4021_);
lean_dec(v___x_4020_);
lean_inc_n(v_stx_2277_, 2);
v___x_4022_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_4023_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4024_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4023_, v_env_4021_, v___x_4022_);
v___x_4025_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4026_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_4024_, v___x_4025_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_4024_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4057_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4029_ = v___x_4026_;
v_isShared_4030_ = v_isSharedCheck_4057_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4026_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4057_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v_fst_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4055_; 
v_fst_4031_ = lean_ctor_get(v_a_4027_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_a_4027_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; 
v_unused_4056_ = lean_ctor_get(v_a_4027_, 1);
lean_dec(v_unused_4056_);
v___x_4033_ = v_a_4027_;
v_isShared_4034_ = v_isSharedCheck_4055_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_fst_4031_);
lean_dec(v_a_4027_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4055_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
if (lean_obj_tag(v_fst_4031_) == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4038_; 
lean_del_object(v___x_4029_);
v___x_4035_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4036_ = l_Lean_MessageData_ofName(v___x_4022_);
lean_inc_ref(v___x_4036_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set_tag(v___x_4033_, 7);
lean_ctor_set(v___x_4033_, 1, v___x_4036_);
lean_ctor_set(v___x_4033_, 0, v___x_4035_);
v___x_4038_ = v___x_4033_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4035_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4039_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_4042_ = l_Lean_indentD(v___x_4041_);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4040_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v___x_4036_);
v___x_4047_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4046_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4048_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4049_;
}
}
else
{
lean_object* v_val_4051_; lean_object* v___x_4053_; 
lean_del_object(v___x_4033_);
lean_dec(v___x_4022_);
lean_dec(v_stx_2277_);
v_val_4051_ = lean_ctor_get(v_fst_4031_, 0);
lean_inc(v_val_4051_);
lean_dec_ref(v_fst_4031_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v_val_4051_);
v___x_4053_ = v___x_4029_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_val_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v___x_4022_);
lean_dec(v_stx_2277_);
v_a_4058_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4026_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4026_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v___x_4066_ = l_Lean_Syntax_getArg(v___x_4018_, v___x_3918_);
lean_dec(v___x_4018_);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77));
v___x_4068_ = l_Lean_Syntax_isOfKind(v___x_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; lean_object* v_env_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4069_ = lean_st_ref_get(v_a_2283_);
v_env_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc_ref(v_env_4070_);
lean_dec(v___x_4069_);
lean_inc_n(v_stx_2277_, 2);
v___x_4071_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_4072_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4073_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4072_, v_env_4070_, v___x_4071_);
v___x_4074_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4075_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_4073_, v___x_4074_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_4073_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4106_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4106_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4106_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v_fst_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4104_; 
v_fst_4080_ = lean_ctor_get(v_a_4076_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_a_4076_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; 
v_unused_4105_ = lean_ctor_get(v_a_4076_, 1);
lean_dec(v_unused_4105_);
v___x_4082_ = v_a_4076_;
v_isShared_4083_ = v_isSharedCheck_4104_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_fst_4080_);
lean_dec(v_a_4076_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4104_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
if (lean_obj_tag(v_fst_4080_) == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
lean_del_object(v___x_4078_);
v___x_4084_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4085_ = l_Lean_MessageData_ofName(v___x_4071_);
lean_inc_ref(v___x_4085_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 7);
lean_ctor_set(v___x_4082_, 1, v___x_4085_);
lean_ctor_set(v___x_4082_, 0, v___x_4084_);
v___x_4087_ = v___x_4082_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4088_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_4091_ = l_Lean_indentD(v___x_4090_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4089_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v___x_4085_);
v___x_4096_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4097_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4098_;
}
}
else
{
lean_object* v_val_4100_; lean_object* v___x_4102_; 
lean_del_object(v___x_4082_);
lean_dec(v___x_4071_);
lean_dec(v_stx_2277_);
v_val_4100_ = lean_ctor_get(v_fst_4080_, 0);
lean_inc(v_val_4100_);
lean_dec_ref(v_fst_4080_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 0, v_val_4100_);
v___x_4102_ = v___x_4078_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_val_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v___x_4071_);
lean_dec(v_stx_2277_);
v_a_4107_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4075_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4075_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_dec(v_stx_2277_);
v___x_4115_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
return v___x_4116_;
}
}
}
}
}
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; uint8_t v___x_4120_; 
v___x_4117_ = lean_unsigned_to_nat(1u);
v___x_4118_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_4117_);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4120_ = l_Lean_Syntax_isOfKind(v___x_4118_, v___x_4119_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v_env_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4121_ = lean_st_ref_get(v_a_2283_);
v_env_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc_ref(v_env_4122_);
lean_dec(v___x_4121_);
lean_inc_n(v_stx_2277_, 2);
v___x_4123_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_4124_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4125_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4124_, v_env_4122_, v___x_4123_);
v___x_4126_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4127_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_4125_, v___x_4126_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_4125_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4158_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4158_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4158_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v_fst_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4156_; 
v_fst_4132_ = lean_ctor_get(v_a_4128_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_a_4128_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v_a_4128_, 1);
lean_dec(v_unused_4157_);
v___x_4134_ = v_a_4128_;
v_isShared_4135_ = v_isSharedCheck_4156_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_fst_4132_);
lean_dec(v_a_4128_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4156_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
if (lean_obj_tag(v_fst_4132_) == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
lean_del_object(v___x_4130_);
v___x_4136_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4137_ = l_Lean_MessageData_ofName(v___x_4123_);
lean_inc_ref(v___x_4137_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 7);
lean_ctor_set(v___x_4134_, 1, v___x_4137_);
lean_ctor_set(v___x_4134_, 0, v___x_4136_);
v___x_4139_ = v___x_4134_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4140_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4139_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_4143_ = l_Lean_indentD(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4141_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
lean_ctor_set(v___x_4147_, 1, v___x_4137_);
v___x_4148_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4147_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
v___x_4150_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4149_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4150_;
}
}
else
{
lean_object* v_val_4152_; lean_object* v___x_4154_; 
lean_del_object(v___x_4134_);
lean_dec(v___x_4123_);
lean_dec(v_stx_2277_);
v_val_4152_ = lean_ctor_get(v_fst_4132_, 0);
lean_inc(v_val_4152_);
lean_dec_ref(v_fst_4132_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v_val_4152_);
v___x_4154_ = v___x_4130_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_val_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec(v___x_4123_);
lean_dec(v_stx_2277_);
v_a_4159_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4127_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4127_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v___x_4167_ = lean_unsigned_to_nat(2u);
v___x_4168_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_4167_);
v___x_4169_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4170_ = l_Lean_Syntax_isOfKind(v___x_4168_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v_env_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4171_ = lean_st_ref_get(v_a_2283_);
v_env_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc_ref(v_env_4172_);
lean_dec(v___x_4171_);
lean_inc_n(v_stx_2277_, 2);
v___x_4173_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_4174_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4175_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4174_, v_env_4172_, v___x_4173_);
v___x_4176_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4177_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_4175_, v___x_4176_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_4175_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4208_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4208_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4208_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v_fst_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4206_; 
v_fst_4182_ = lean_ctor_get(v_a_4178_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_a_4178_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; 
v_unused_4207_ = lean_ctor_get(v_a_4178_, 1);
lean_dec(v_unused_4207_);
v___x_4184_ = v_a_4178_;
v_isShared_4185_ = v_isSharedCheck_4206_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_fst_4182_);
lean_dec(v_a_4178_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4206_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
if (lean_obj_tag(v_fst_4182_) == 0)
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4189_; 
lean_del_object(v___x_4180_);
v___x_4186_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4187_ = l_Lean_MessageData_ofName(v___x_4173_);
lean_inc_ref(v___x_4187_);
if (v_isShared_4185_ == 0)
{
lean_ctor_set_tag(v___x_4184_, 7);
lean_ctor_set(v___x_4184_, 1, v___x_4187_);
lean_ctor_set(v___x_4184_, 0, v___x_4186_);
v___x_4189_ = v___x_4184_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4186_);
lean_ctor_set(v_reuseFailAlloc_4201_, 1, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4190_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4189_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_4193_ = l_Lean_indentD(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4191_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4194_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
lean_ctor_set(v___x_4197_, 1, v___x_4187_);
v___x_4198_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4197_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4199_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4200_;
}
}
else
{
lean_object* v_val_4202_; lean_object* v___x_4204_; 
lean_del_object(v___x_4184_);
lean_dec(v___x_4173_);
lean_dec(v_stx_2277_);
v_val_4202_ = lean_ctor_get(v_fst_4182_, 0);
lean_inc(v_val_4202_);
lean_dec_ref(v_fst_4182_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v_val_4202_);
v___x_4204_ = v___x_4180_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_val_4202_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec(v___x_4173_);
lean_dec(v_stx_2277_);
v_a_4209_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4177_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4177_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_dec(v_stx_2277_);
v___x_4217_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
return v___x_4218_;
}
}
}
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; 
v___x_4219_ = lean_unsigned_to_nat(1u);
v___x_4220_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_4219_);
v___x_4221_ = l_Lean_Syntax_isNone(v___x_4220_);
if (v___x_4221_ == 0)
{
uint8_t v___x_4222_; 
v___x_4222_ = l_Lean_Syntax_matchesNull(v___x_4220_, v___x_4219_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; lean_object* v_env_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
lean_del_object(v___x_2314_);
v___x_4223_ = lean_st_ref_get(v_a_2283_);
v_env_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc_ref(v_env_4224_);
lean_dec(v___x_4223_);
lean_inc_n(v_stx_2277_, 2);
v___x_4225_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_4226_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4227_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4226_, v_env_4224_, v___x_4225_);
v___x_4228_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4229_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_4227_, v___x_4228_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_4227_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4260_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4260_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4260_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v_fst_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4258_; 
v_fst_4234_ = lean_ctor_get(v_a_4230_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v_a_4230_);
if (v_isSharedCheck_4258_ == 0)
{
lean_object* v_unused_4259_; 
v_unused_4259_ = lean_ctor_get(v_a_4230_, 1);
lean_dec(v_unused_4259_);
v___x_4236_ = v_a_4230_;
v_isShared_4237_ = v_isSharedCheck_4258_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_fst_4234_);
lean_dec(v_a_4230_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4258_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
if (lean_obj_tag(v_fst_4234_) == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4241_; 
lean_del_object(v___x_4232_);
v___x_4238_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4239_ = l_Lean_MessageData_ofName(v___x_4225_);
lean_inc_ref(v___x_4239_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set_tag(v___x_4236_, 7);
lean_ctor_set(v___x_4236_, 1, v___x_4239_);
lean_ctor_set(v___x_4236_, 0, v___x_4238_);
v___x_4241_ = v___x_4236_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4238_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4242_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_4245_ = l_Lean_indentD(v___x_4244_);
v___x_4246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4243_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
lean_ctor_set(v___x_4249_, 1, v___x_4239_);
v___x_4250_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4249_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4251_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4252_;
}
}
else
{
lean_object* v_val_4254_; lean_object* v___x_4256_; 
lean_del_object(v___x_4236_);
lean_dec(v___x_4225_);
lean_dec(v_stx_2277_);
v_val_4254_ = lean_ctor_get(v_fst_4234_, 0);
lean_inc(v_val_4254_);
lean_dec_ref(v_fst_4234_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v_val_4254_);
v___x_4256_ = v___x_4232_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_val_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec(v___x_4225_);
lean_dec(v_stx_2277_);
v_a_4261_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4229_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4229_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
v___y_2402_ = v_a_2278_;
v___y_2403_ = v_a_2279_;
v___y_2404_ = v_a_2280_;
v___y_2405_ = v_a_2281_;
v___y_2406_ = v_a_2282_;
v___y_2407_ = v_a_2283_;
goto v___jp_2401_;
}
}
else
{
lean_dec(v___x_4220_);
v___y_2402_ = v_a_2278_;
v___y_2403_ = v_a_2279_;
v___y_2404_ = v_a_2280_;
v___y_2405_ = v_a_2281_;
v___y_2406_ = v_a_2282_;
v___y_2407_ = v_a_2283_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
lean_del_object(v___x_2314_);
v___x_4269_ = lean_unsigned_to_nat(1u);
v___x_4270_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_4269_);
lean_dec(v_stx_2277_);
v___x_4271_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4270_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4271_;
}
}
else
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_del_object(v___x_2314_);
lean_dec(v_stx_2277_);
v___x_4272_ = lean_unsigned_to_nat(1u);
v___x_4273_ = l_Lean_NameSet_empty;
v___x_4274_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*2, v___x_2518_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*2 + 1, v___x_2518_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*2 + 2, v___x_2518_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
lean_del_object(v___x_2314_);
v___x_4276_ = lean_unsigned_to_nat(0u);
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_4281_);
v___x_4283_ = l_Lean_Syntax_isNone(v___x_4282_);
if (v___x_4283_ == 0)
{
uint8_t v___x_4284_; 
v___x_4284_ = l_Lean_Syntax_matchesNull(v___x_4282_, v___x_4281_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; lean_object* v_env_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4285_ = lean_st_ref_get(v_a_2283_);
v_env_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc_ref(v_env_4286_);
lean_dec(v___x_4285_);
lean_inc_n(v_stx_2277_, 2);
v___x_4287_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_4288_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4289_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4288_, v_env_4286_, v___x_4287_);
v___x_4290_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4291_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_4289_, v___x_4290_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_4289_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4322_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4322_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4322_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v_fst_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4320_; 
v_fst_4296_ = lean_ctor_get(v_a_4292_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_a_4292_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; 
v_unused_4321_ = lean_ctor_get(v_a_4292_, 1);
lean_dec(v_unused_4321_);
v___x_4298_ = v_a_4292_;
v_isShared_4299_ = v_isSharedCheck_4320_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_fst_4296_);
lean_dec(v_a_4292_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4320_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
if (lean_obj_tag(v_fst_4296_) == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_del_object(v___x_4294_);
v___x_4300_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4301_ = l_Lean_MessageData_ofName(v___x_4287_);
lean_inc_ref(v___x_4301_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set_tag(v___x_4298_, 7);
lean_ctor_set(v___x_4298_, 1, v___x_4301_);
lean_ctor_set(v___x_4298_, 0, v___x_4300_);
v___x_4303_ = v___x_4298_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v___x_4301_);
v___x_4303_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4304_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_4307_ = l_Lean_indentD(v___x_4306_);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4305_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4308_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
lean_ctor_set(v___x_4311_, 1, v___x_4301_);
v___x_4312_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4313_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_4314_;
}
}
else
{
lean_object* v_val_4316_; lean_object* v___x_4318_; 
lean_del_object(v___x_4298_);
lean_dec(v___x_4287_);
lean_dec(v_stx_2277_);
v_val_4316_ = lean_ctor_get(v_fst_4296_, 0);
lean_inc(v_val_4316_);
lean_dec_ref(v_fst_4296_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v_val_4316_);
v___x_4318_ = v___x_4294_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_val_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v___x_4287_);
lean_dec(v_stx_2277_);
v_a_4323_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4291_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4291_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_dec(v_stx_2277_);
goto v___jp_4277_;
}
}
else
{
lean_dec(v___x_4282_);
lean_dec(v_stx_2277_);
goto v___jp_4277_;
}
v___jp_4277_:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = l_Lean_NameSet_empty;
v___x_4279_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4279_, 0, v___x_4276_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
lean_ctor_set_uint8(v___x_4279_, sizeof(void*)*2, v___x_2516_);
lean_ctor_set_uint8(v___x_4279_, sizeof(void*)*2 + 1, v___x_2516_);
lean_ctor_set_uint8(v___x_4279_, sizeof(void*)*2 + 2, v___x_2514_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
lean_del_object(v___x_2314_);
lean_dec(v_stx_2277_);
v___x_4331_ = lean_unsigned_to_nat(0u);
v___x_4332_ = l_Lean_NameSet_empty;
v___x_4333_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4333_, 0, v___x_4331_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*2, v___x_2513_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*2 + 1, v___x_2514_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*2 + 2, v___x_2513_);
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
return v___x_4334_;
}
}
else
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
lean_del_object(v___x_2314_);
lean_dec(v_stx_2277_);
v___x_4335_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78);
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
return v___x_4336_;
}
v___jp_2330_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2337_ = lean_unsigned_to_nat(2u);
v___x_2338_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2337_);
v___x_2339_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2340_ = l_Lean_Syntax_isOfKind(v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; lean_object* v_env_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2341_ = lean_st_ref_get(v___y_2336_);
v_env_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_ref(v_env_2342_);
lean_dec(v___x_2341_);
lean_inc_n(v_stx_2277_, 2);
v___x_2343_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2344_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2345_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2344_, v_env_2342_, v___x_2343_);
v___x_2346_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2347_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2345_, v___x_2346_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___x_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2378_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2378_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2378_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_fst_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2376_; 
v_fst_2352_ = lean_ctor_get(v_a_2348_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_a_2348_, 1);
lean_dec(v_unused_2377_);
v___x_2354_ = v_a_2348_;
v_isShared_2355_ = v_isSharedCheck_2376_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_fst_2352_);
lean_dec(v_a_2348_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2376_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
if (lean_obj_tag(v_fst_2352_) == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_del_object(v___x_2350_);
v___x_2356_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2357_ = l_Lean_MessageData_ofName(v___x_2343_);
lean_inc_ref(v___x_2357_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 7);
lean_ctor_set(v___x_2354_, 1, v___x_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2360_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2363_ = l_Lean_indentD(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2361_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v___x_2357_);
v___x_2368_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2369_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2370_;
}
}
else
{
lean_object* v_val_2372_; lean_object* v___x_2374_; 
lean_del_object(v___x_2354_);
lean_dec(v___x_2343_);
lean_dec(v_stx_2277_);
v_val_2372_ = lean_ctor_get(v_fst_2352_, 0);
lean_inc(v_val_2372_);
lean_dec_ref(v_fst_2352_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_val_2372_);
v___x_2374_ = v___x_2350_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_val_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v___x_2343_);
lean_dec(v_stx_2277_);
v_a_2379_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2347_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2347_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2387_ = lean_unsigned_to_nat(7u);
v___x_2388_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2387_);
v___x_2389_ = lean_unsigned_to_nat(8u);
v___x_2390_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2389_);
lean_dec(v_stx_2277_);
v___x_2391_ = l_Lean_Syntax_getOptional_x3f(v___x_2390_);
lean_dec(v___x_2390_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_box(0);
v___y_2286_ = v___y_2332_;
v___y_2287_ = v___x_2388_;
v___y_2288_ = v___y_2336_;
v___y_2289_ = v___y_2331_;
v___y_2290_ = v___y_2334_;
v___y_2291_ = v___y_2333_;
v___y_2292_ = v___y_2335_;
v___y_2293_ = v___x_2392_;
goto v___jp_2285_;
}
else
{
lean_object* v_val_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v_val_2393_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_val_2393_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_val_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
v___y_2286_ = v___y_2332_;
v___y_2287_ = v___x_2388_;
v___y_2288_ = v___y_2336_;
v___y_2289_ = v___y_2331_;
v___y_2290_ = v___y_2334_;
v___y_2291_ = v___y_2333_;
v___y_2292_ = v___y_2335_;
v___y_2293_ = v___x_2398_;
goto v___jp_2285_;
}
}
}
}
}
v___jp_2401_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2408_ = lean_unsigned_to_nat(2u);
v___x_2409_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2408_);
v___x_2410_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2411_ = l_Lean_Syntax_isOfKind(v___x_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v_env_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_del_object(v___x_2314_);
v___x_2412_ = lean_st_ref_get(v___y_2407_);
v_env_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_env_2413_);
lean_dec(v___x_2412_);
lean_inc_n(v_stx_2277_, 2);
v___x_2414_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2415_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2416_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2415_, v_env_2413_, v___x_2414_);
v___x_2417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2418_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2416_, v___x_2417_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___x_2416_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2449_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2449_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2449_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_fst_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2447_; 
v_fst_2423_ = lean_ctor_get(v_a_2419_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_a_2419_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v_a_2419_, 1);
lean_dec(v_unused_2448_);
v___x_2425_ = v_a_2419_;
v_isShared_2426_ = v_isSharedCheck_2447_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_fst_2423_);
lean_dec(v_a_2419_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2447_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
if (lean_obj_tag(v_fst_2423_) == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_del_object(v___x_2421_);
v___x_2427_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2428_ = l_Lean_MessageData_ofName(v___x_2414_);
lean_inc_ref(v___x_2428_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set_tag(v___x_2425_, 7);
lean_ctor_set(v___x_2425_, 1, v___x_2428_);
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2430_ = v___x_2425_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2431_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2434_ = l_Lean_indentD(v___x_2433_);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2432_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2428_);
v___x_2439_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2440_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
return v___x_2441_;
}
}
else
{
lean_object* v_val_2443_; lean_object* v___x_2445_; 
lean_del_object(v___x_2425_);
lean_dec(v___x_2414_);
lean_dec(v_stx_2277_);
v_val_2443_ = lean_ctor_get(v_fst_2423_, 0);
lean_inc(v_val_2443_);
lean_dec_ref(v_fst_2423_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_val_2443_);
v___x_2445_ = v___x_2421_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_val_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v___x_2414_);
lean_dec(v_stx_2277_);
v_a_2450_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2418_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2418_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2458_ = lean_unsigned_to_nat(3u);
v___x_2459_ = l_Lean_Syntax_getArg(v_stx_2277_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2461_ = l_Lean_Syntax_isOfKind(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v_env_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_del_object(v___x_2314_);
v___x_2462_ = lean_st_ref_get(v___y_2407_);
v_env_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_ref(v_env_2463_);
lean_dec(v___x_2462_);
lean_inc_n(v_stx_2277_, 2);
v___x_2464_ = l_Lean_Syntax_getKind(v_stx_2277_);
v___x_2465_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2466_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2465_, v_env_2463_, v___x_2464_);
v___x_2467_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2468_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2277_, v___x_2466_, v___x_2467_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___x_2466_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2499_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2499_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2499_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_fst_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2497_; 
v_fst_2473_ = lean_ctor_get(v_a_2469_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v_a_2469_, 1);
lean_dec(v_unused_2498_);
v___x_2475_ = v_a_2469_;
v_isShared_2476_ = v_isSharedCheck_2497_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_fst_2473_);
lean_dec(v_a_2469_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2497_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
if (lean_obj_tag(v_fst_2473_) == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_del_object(v___x_2471_);
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2478_ = l_Lean_MessageData_ofName(v___x_2464_);
lean_inc_ref(v___x_2478_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set_tag(v___x_2475_, 7);
lean_ctor_set(v___x_2475_, 1, v___x_2478_);
lean_ctor_set(v___x_2475_, 0, v___x_2477_);
v___x_2480_ = v___x_2475_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2481_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_MessageData_ofSyntax(v_stx_2277_);
v___x_2484_ = l_Lean_indentD(v___x_2483_);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2482_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2478_);
v___x_2489_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2490_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
return v___x_2491_;
}
}
else
{
lean_object* v_val_2493_; lean_object* v___x_2495_; 
lean_del_object(v___x_2475_);
lean_dec(v___x_2464_);
lean_dec(v_stx_2277_);
v_val_2493_ = lean_ctor_get(v_fst_2473_, 0);
lean_inc(v_val_2493_);
lean_dec_ref(v_fst_2473_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v_val_2493_);
v___x_2495_ = v___x_2471_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_val_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v___x_2464_);
lean_dec(v_stx_2277_);
v_a_2500_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2468_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2468_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_dec(v_stx_2277_);
v___x_2508_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2508_);
v___x_2510_ = v___x_2314_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec(v_stx_2277_);
v_a_4338_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_2311_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_2311_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
v___jp_2285_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2294_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___y_2287_);
v___x_2297_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2294_, v___x_2295_, v___x_2296_, v___y_2293_, v___y_2289_, v___y_2286_, v___y_2291_, v___y_2290_, v___y_2292_, v___y_2288_);
return v___x_2297_;
}
v___jp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2299_, v_bodyInfo_2300_);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
v___jp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2304_, v_bodyInfo_2305_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4346_, size_t v_sz_4347_, size_t v_i_4348_, lean_object* v_b_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
uint8_t v___x_4357_; 
v___x_4357_ = lean_usize_dec_lt(v_i_4348_, v_sz_4347_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; 
v___x_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4358_, 0, v_b_4349_);
return v___x_4358_;
}
else
{
uint8_t v_breaks_4359_; uint8_t v_continues_4360_; uint8_t v_returnsEarly_4361_; lean_object* v_numRegularExits_4362_; lean_object* v_reassigns_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
v_breaks_4359_ = lean_ctor_get_uint8(v_b_4349_, sizeof(void*)*2);
v_continues_4360_ = lean_ctor_get_uint8(v_b_4349_, sizeof(void*)*2 + 1);
v_returnsEarly_4361_ = lean_ctor_get_uint8(v_b_4349_, sizeof(void*)*2 + 2);
v_numRegularExits_4362_ = lean_ctor_get(v_b_4349_, 0);
v_reassigns_4363_ = lean_ctor_get(v_b_4349_, 1);
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = lean_nat_dec_eq(v_numRegularExits_4362_, v___x_4364_);
if (v___x_4365_ == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4367_; 
lean_inc(v_reassigns_4363_);
lean_dec_ref(v_b_4349_);
v_a_4366_ = lean_array_uget_borrowed(v_as_4346_, v_i_4348_);
lean_inc(v_a_4366_);
v___x_4367_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4366_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; uint8_t v___y_4370_; uint8_t v___y_4371_; uint8_t v___y_4372_; uint8_t v___y_4387_; uint8_t v___y_4388_; uint8_t v___y_4391_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref(v___x_4367_);
if (v_breaks_4359_ == 0)
{
uint8_t v_breaks_4393_; 
v_breaks_4393_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*2);
v___y_4391_ = v_breaks_4393_;
goto v___jp_4390_;
}
else
{
v___y_4391_ = v___x_4357_;
goto v___jp_4390_;
}
v___jp_4369_:
{
lean_object* v_numRegularExits_4373_; lean_object* v_reassigns_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4385_; 
v_numRegularExits_4373_ = lean_ctor_get(v_a_4368_, 0);
v_reassigns_4374_ = lean_ctor_get(v_a_4368_, 1);
v_isSharedCheck_4385_ = !lean_is_exclusive(v_a_4368_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4376_ = v_a_4368_;
v_isShared_4377_ = v_isSharedCheck_4385_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_reassigns_4374_);
lean_inc(v_numRegularExits_4373_);
lean_dec(v_a_4368_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4385_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = l_Lean_NameSet_append(v_reassigns_4363_, v_reassigns_4374_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 1, v___x_4378_);
v___x_4380_ = v___x_4376_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_numRegularExits_4373_);
lean_ctor_set(v_reuseFailAlloc_4384_, 1, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
size_t v___x_4381_; size_t v___x_4382_; 
lean_ctor_set_uint8(v___x_4380_, sizeof(void*)*2, v___y_4371_);
lean_ctor_set_uint8(v___x_4380_, sizeof(void*)*2 + 1, v___y_4370_);
lean_ctor_set_uint8(v___x_4380_, sizeof(void*)*2 + 2, v___y_4372_);
v___x_4381_ = ((size_t)1ULL);
v___x_4382_ = lean_usize_add(v_i_4348_, v___x_4381_);
v_i_4348_ = v___x_4382_;
v_b_4349_ = v___x_4380_;
goto _start;
}
}
}
v___jp_4386_:
{
if (v_returnsEarly_4361_ == 0)
{
uint8_t v_returnsEarly_4389_; 
v_returnsEarly_4389_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*2 + 2);
v___y_4370_ = v___y_4388_;
v___y_4371_ = v___y_4387_;
v___y_4372_ = v_returnsEarly_4389_;
goto v___jp_4369_;
}
else
{
v___y_4370_ = v___y_4388_;
v___y_4371_ = v___y_4387_;
v___y_4372_ = v___x_4357_;
goto v___jp_4369_;
}
}
v___jp_4390_:
{
if (v_continues_4360_ == 0)
{
uint8_t v_continues_4392_; 
v_continues_4392_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*2 + 1);
v___y_4387_ = v___y_4391_;
v___y_4388_ = v_continues_4392_;
goto v___jp_4386_;
}
else
{
v___y_4387_ = v___y_4391_;
v___y_4388_ = v___x_4357_;
goto v___jp_4386_;
}
}
}
else
{
lean_dec(v_reassigns_4363_);
return v___x_4367_;
}
}
else
{
lean_object* v___x_4394_; 
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v_b_4349_);
return v___x_4394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_info_4403_; lean_object* v___x_4404_; size_t v_sz_4405_; size_t v___x_4406_; lean_object* v___x_4407_; 
v_info_4403_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4404_ = l_Lean_Parser_Term_getDoElems(v_stx_4395_);
v_sz_4405_ = lean_array_size(v___x_4404_);
v___x_4406_ = ((size_t)0ULL);
v___x_4407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4404_, v_sz_4405_, v___x_4406_, v_info_4403_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec_ref(v___x_4404_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
lean_dec(v_a_4414_);
lean_dec_ref(v_a_4413_);
lean_dec(v_a_4412_);
lean_dec_ref(v_a_4411_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4426_, lean_object* v_sz_4427_, lean_object* v_i_4428_, lean_object* v_b_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
size_t v_sz_boxed_4437_; size_t v_i_boxed_4438_; lean_object* v_res_4439_; 
v_sz_boxed_4437_ = lean_unbox_usize(v_sz_4427_);
lean_dec(v_sz_4427_);
v_i_boxed_4438_ = lean_unbox_usize(v_i_4428_);
lean_dec(v_i_4428_);
v_res_4439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4426_, v_sz_boxed_4437_, v_i_boxed_4438_, v_b_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec_ref(v_as_4426_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4440_, lean_object* v_sz_4441_, lean_object* v_i_4442_, lean_object* v_b_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
size_t v_sz_boxed_4451_; size_t v_i_boxed_4452_; lean_object* v_res_4453_; 
v_sz_boxed_4451_ = lean_unbox_usize(v_sz_4441_);
lean_dec(v_sz_4441_);
v_i_boxed_4452_ = lean_unbox_usize(v_i_4442_);
lean_dec(v_i_4442_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4440_, v_sz_boxed_4451_, v_i_boxed_4452_, v_b_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec_ref(v_as_4440_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4454_, lean_object* v_rhs_x3f_4455_, lean_object* v_otherwise_x3f_4456_, lean_object* v_body_x3f_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4454_, v_rhs_x3f_4455_, v_otherwise_x3f_4456_, v_body_x3f_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4466_, lean_object* v_as_4467_, lean_object* v_sz_4468_, lean_object* v_i_4469_, lean_object* v_b_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
uint8_t v___x_282367__boxed_4478_; size_t v_sz_boxed_4479_; size_t v_i_boxed_4480_; lean_object* v_res_4481_; 
v___x_282367__boxed_4478_ = lean_unbox(v___x_4466_);
v_sz_boxed_4479_ = lean_unbox_usize(v_sz_4468_);
lean_dec(v_sz_4468_);
v_i_boxed_4480_ = lean_unbox_usize(v_i_4469_);
lean_dec(v_i_4469_);
v_res_4481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_282367__boxed_4478_, v_as_4467_, v_sz_boxed_4479_, v_i_boxed_4480_, v_b_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec_ref(v_as_4467_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4482_, lean_object* v_as_4483_, lean_object* v_sz_4484_, lean_object* v_i_4485_, lean_object* v_b_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
uint8_t v___x_282418__boxed_4494_; size_t v_sz_boxed_4495_; size_t v_i_boxed_4496_; lean_object* v_res_4497_; 
v___x_282418__boxed_4494_ = lean_unbox(v___x_4482_);
v_sz_boxed_4495_ = lean_unbox_usize(v_sz_4484_);
lean_dec(v_sz_4484_);
v_i_boxed_4496_ = lean_unbox_usize(v_i_4485_);
lean_dec(v_i_4485_);
v_res_4497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_282418__boxed_4494_, v_as_4483_, v_sz_boxed_4495_, v_i_boxed_4496_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v_as_4483_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4498_, lean_object* v_sz_4499_, lean_object* v_i_4500_, lean_object* v_b_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
size_t v_sz_boxed_4509_; size_t v_i_boxed_4510_; lean_object* v_res_4511_; 
v_sz_boxed_4509_ = lean_unbox_usize(v_sz_4499_);
lean_dec(v_sz_4499_);
v_i_boxed_4510_ = lean_unbox_usize(v_i_4500_);
lean_dec(v_i_4500_);
v_res_4511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4498_, v_sz_boxed_4509_, v_i_boxed_4510_, v_b_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec_ref(v_as_4498_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4512_, lean_object* v_decl_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
uint8_t v_reassignment_boxed_4521_; lean_object* v_res_4522_; 
v_reassignment_boxed_4521_ = lean_unbox(v_reassignment_4512_);
v_res_4522_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4521_, v_decl_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4550_, lean_object* v_ref_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4551_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4560_, lean_object* v_ref_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4560_, v_ref_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4570_, lean_object* v_x_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4580_, lean_object* v_x_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4580_, v_x_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4590_, lean_object* v_as_4591_, lean_object* v_as_x27_4592_, lean_object* v_b_4593_, lean_object* v_a_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4590_, v_as_x27_4592_, v_b_4593_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4603_, lean_object* v_as_4604_, lean_object* v_as_x27_4605_, lean_object* v_b_4606_, lean_object* v_a_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4603_, v_as_4604_, v_as_x27_4605_, v_b_4606_, v_a_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v_as_x27_4605_);
lean_dec(v_as_4604_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4616_, lean_object* v_msg_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4626_, lean_object* v_msg_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4626_, v_msg_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4636_, lean_object* v_msg_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4636_, v_msg_4637_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4646_, lean_object* v_msg_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4646_, v_msg_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4656_, lean_object* v_as_x27_4657_, lean_object* v_b_4658_, lean_object* v_a_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4657_, v_b_4658_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4668_, lean_object* v_as_x27_4669_, lean_object* v_b_4670_, lean_object* v_a_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4668_, v_as_x27_4669_, v_b_4670_, v_a_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v_as_x27_4669_);
lean_dec(v_as_4668_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4680_, lean_object* v_ref_4681_, lean_object* v_msg_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4681_, v_msg_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4691_, lean_object* v_ref_4692_, lean_object* v_msg_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4691_, v_ref_4692_, v_msg_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v_ref_4692_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4702_, lean_object* v_macroStack_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4702_, v_macroStack_4703_, v___y_4708_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4712_, lean_object* v_macroStack_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4712_, v_macroStack_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4722_, lean_object* v_m_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4723_, v_a_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4726_, lean_object* v_m_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4726_, v_m_4727_, v_a_4728_);
lean_dec(v_a_4728_);
lean_dec_ref(v_m_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4730_, lean_object* v_x_4731_, lean_object* v_x_4732_){
_start:
{
uint8_t v___x_4733_; 
v___x_4733_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4731_, v_x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4734_, lean_object* v_x_4735_, lean_object* v_x_4736_){
_start:
{
uint8_t v_res_4737_; lean_object* v_r_4738_; 
v_res_4737_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4734_, v_x_4735_, v_x_4736_);
lean_dec_ref(v_x_4736_);
lean_dec_ref(v_x_4735_);
v_r_4738_ = lean_box(v_res_4737_);
return v_r_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4739_, lean_object* v_a_4740_, lean_object* v_x_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4740_, v_x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4743_, lean_object* v_a_4744_, lean_object* v_x_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4743_, v_a_4744_, v_x_4745_);
lean_dec(v_x_4745_);
lean_dec(v_a_4744_);
return v_res_4746_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4747_, lean_object* v_x_4748_, size_t v_x_4749_, lean_object* v_x_4750_){
_start:
{
uint8_t v___x_4751_; 
v___x_4751_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4748_, v_x_4749_, v_x_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4752_, lean_object* v_x_4753_, lean_object* v_x_4754_, lean_object* v_x_4755_){
_start:
{
size_t v_x_288075__boxed_4756_; uint8_t v_res_4757_; lean_object* v_r_4758_; 
v_x_288075__boxed_4756_ = lean_unbox_usize(v_x_4754_);
lean_dec(v_x_4754_);
v_res_4757_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4752_, v_x_4753_, v_x_288075__boxed_4756_, v_x_4755_);
lean_dec_ref(v_x_4755_);
lean_dec_ref(v_x_4753_);
v_r_4758_ = lean_box(v_res_4757_);
return v_r_4758_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4759_, lean_object* v_keys_4760_, lean_object* v_vals_4761_, lean_object* v_heq_4762_, lean_object* v_i_4763_, lean_object* v_k_4764_){
_start:
{
uint8_t v___x_4765_; 
v___x_4765_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4760_, v_i_4763_, v_k_4764_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4766_, lean_object* v_keys_4767_, lean_object* v_vals_4768_, lean_object* v_heq_4769_, lean_object* v_i_4770_, lean_object* v_k_4771_){
_start:
{
uint8_t v_res_4772_; lean_object* v_r_4773_; 
v_res_4772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4766_, v_keys_4767_, v_vals_4768_, v_heq_4769_, v_i_4770_, v_k_4771_);
lean_dec_ref(v_k_4771_);
lean_dec_ref(v_vals_4768_);
lean_dec_ref(v_keys_4767_);
v_r_4773_ = lean_box(v_res_4772_);
return v_r_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v_a_4787_);
lean_dec_ref(v_a_4786_);
lean_dec(v_a_4785_);
lean_dec_ref(v_a_4784_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
return v_res_4809_;
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
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
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
