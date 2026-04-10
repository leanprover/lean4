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
lean_inc_n(v_macroStack_366_, 2);
v___x_367_ = l_Lean_Elab_getBetterRef(v_ref_363_, v_macroStack_366_);
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
uint8_t v___x_279696__boxed_490_; uint8_t v___x_279697__boxed_491_; size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v___x_279696__boxed_490_ = lean_unbox(v___x_484_);
v___x_279697__boxed_491_ = lean_unbox(v___x_485_);
v_i_boxed_492_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_488_);
lean_dec(v_stop_488_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_279696__boxed_490_, v___x_279697__boxed_491_, v_as_486_, v_i_boxed_492_, v_stop_boxed_493_, v_b_489_);
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
size_t v_x_280226__boxed_828_; uint8_t v_res_829_; lean_object* v_r_830_; 
v_x_280226__boxed_828_ = lean_unbox_usize(v_x_826_);
lean_dec(v_x_826_);
v_res_829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_825_, v_x_280226__boxed_828_, v_x_827_);
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
lean_inc(v_head_1114_);
v_tail_1115_ = lean_ctor_get(v_as_x27_1104_, 1);
lean_inc(v_tail_1115_);
lean_dec_ref(v_as_x27_1104_);
v___x_1116_ = 1;
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
lean_dec(v_tail_1115_);
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
lean_object* v_head_1416_; lean_object* v_tail_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v_b_1407_);
v_head_1416_ = lean_ctor_get(v_as_x27_1406_, 0);
v_tail_1417_ = lean_ctor_get(v_as_x27_1406_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_as_x27_1406_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1419_ = v_as_x27_1406_;
v_isShared_1420_ = v_isSharedCheck_1459_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_tail_1417_);
lean_inc(v_head_1416_);
lean_dec(v_as_x27_1406_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1459_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_value_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_value_1421_ = lean_ctor_get(v_head_1416_, 1);
lean_inc(v_value_1421_);
lean_dec(v_head_1416_);
v___x_1422_ = lean_box(0);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v_stx_1405_);
v___x_1423_ = lean_apply_8(v_value_1421_, v_stx_1405_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, lean_box(0));
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_tail_1417_);
lean_dec(v_stx_1405_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1435_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1435_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1424_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 0);
lean_ctor_set(v___x_1419_, 1, v___x_1422_);
lean_ctor_set(v___x_1419_, 0, v___x_1428_);
v___x_1430_ = v___x_1419_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1422_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1430_);
v___x_1432_ = v___x_1426_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1458_; 
lean_del_object(v___x_1419_);
v_a_1436_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1438_ = v___x_1423_;
v_isShared_1439_ = v_isSharedCheck_1458_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1423_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1458_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___y_1443_; uint8_t v___x_1456_; 
v___x_1440_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1441_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1456_ = l_Lean_Exception_isInterrupt(v_a_1436_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; 
lean_inc(v_a_1436_);
v___x_1457_ = l_Lean_Exception_isRuntime(v_a_1436_);
v___y_1443_ = v___x_1457_;
goto v___jp_1442_;
}
else
{
v___y_1443_ = v___x_1456_;
goto v___jp_1442_;
}
v___jp_1442_:
{
if (v___y_1443_ == 0)
{
if (lean_obj_tag(v_a_1436_) == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_tail_1417_);
lean_dec(v_stx_1405_);
if (v_isShared_1439_ == 0)
{
v___x_1445_ = v___x_1438_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1436_);
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
lean_object* v_id_1447_; uint8_t v___x_1448_; 
v_id_1447_ = lean_ctor_get(v_a_1436_, 0);
v___x_1448_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1441_, v_id_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1450_; 
lean_dec(v_tail_1417_);
lean_dec(v_stx_1405_);
if (v_isShared_1439_ == 0)
{
v___x_1450_ = v___x_1438_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1436_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
lean_dec_ref(v_a_1436_);
lean_del_object(v___x_1438_);
v_as_x27_1406_ = v_tail_1417_;
v_b_1407_ = v___x_1440_;
goto _start;
}
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_tail_1417_);
lean_dec(v_stx_1405_);
if (v_isShared_1439_ == 0)
{
v___x_1454_ = v___x_1438_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1436_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1460_, lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1460_, v_as_x27_1461_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1473_, lean_object* v_rhs_x3f_1474_, lean_object* v_otherwise_x3f_1475_, lean_object* v_body_x3f_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
uint8_t v___y_1485_; uint8_t v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v_body_1495_; lean_object* v___y_1515_; lean_object* v_otherwise_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v_rhs_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; 
if (lean_obj_tag(v_rhs_x3f_1474_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1528_ = v___x_1539_;
v___y_1529_ = v_a_1477_;
v___y_1530_ = v_a_1478_;
v___y_1531_ = v_a_1479_;
v___y_1532_ = v_a_1480_;
v___y_1533_ = v_a_1481_;
v___y_1534_ = v_a_1482_;
goto v___jp_1527_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; 
v_val_1540_ = lean_ctor_get(v_rhs_x3f_1474_, 0);
lean_inc(v_val_1540_);
lean_dec_ref(v_rhs_x3f_1474_);
v___x_1541_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1540_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v_rhs_1528_ = v_a_1542_;
v___y_1529_ = v_a_1477_;
v___y_1530_ = v_a_1478_;
v___y_1531_ = v_a_1479_;
v___y_1532_ = v_a_1480_;
v___y_1533_ = v_a_1481_;
v___y_1534_ = v_a_1482_;
goto v___jp_1527_;
}
else
{
lean_dec(v_body_x3f_1476_);
lean_dec(v_otherwise_x3f_1475_);
lean_dec_ref(v_reassigned_1473_);
return v___x_1541_;
}
}
v___jp_1484_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1490_, 0, v___y_1487_);
lean_ctor_set(v___x_1490_, 1, v___y_1489_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*2, v___y_1486_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*2 + 1, v___y_1488_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*2 + 2, v___y_1485_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
v___jp_1492_:
{
lean_object* v___x_1496_; lean_object* v_info_1497_; uint8_t v_breaks_1498_; uint8_t v_continues_1499_; uint8_t v_returnsEarly_1500_; lean_object* v_numRegularExits_1501_; lean_object* v_reassigns_1502_; size_t v_sz_1503_; size_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1496_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1495_, v___y_1493_);
v_info_1497_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1494_, v___x_1496_);
v_breaks_1498_ = lean_ctor_get_uint8(v_info_1497_, sizeof(void*)*2);
v_continues_1499_ = lean_ctor_get_uint8(v_info_1497_, sizeof(void*)*2 + 1);
v_returnsEarly_1500_ = lean_ctor_get_uint8(v_info_1497_, sizeof(void*)*2 + 2);
v_numRegularExits_1501_ = lean_ctor_get(v_info_1497_, 0);
lean_inc(v_numRegularExits_1501_);
v_reassigns_1502_ = lean_ctor_get(v_info_1497_, 1);
lean_inc(v_reassigns_1502_);
lean_dec_ref(v_info_1497_);
v_sz_1503_ = lean_array_size(v_reassigned_1473_);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1503_, v___x_1504_, v_reassigned_1473_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_array_get_size(v___x_1505_);
v___x_1508_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec_ref(v___x_1505_);
v___y_1485_ = v_returnsEarly_1500_;
v___y_1486_ = v_breaks_1498_;
v___y_1487_ = v_numRegularExits_1501_;
v___y_1488_ = v_continues_1499_;
v___y_1489_ = v_reassigns_1502_;
goto v___jp_1484_;
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_le(v___x_1507_, v___x_1507_);
if (v___x_1509_ == 0)
{
if (v___x_1508_ == 0)
{
lean_dec_ref(v___x_1505_);
v___y_1485_ = v_returnsEarly_1500_;
v___y_1486_ = v_breaks_1498_;
v___y_1487_ = v_numRegularExits_1501_;
v___y_1488_ = v_continues_1499_;
v___y_1489_ = v_reassigns_1502_;
goto v___jp_1484_;
}
else
{
size_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_usize_of_nat(v___x_1507_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1505_, v___x_1504_, v___x_1510_, v_reassigns_1502_);
lean_dec_ref(v___x_1505_);
v___y_1485_ = v_returnsEarly_1500_;
v___y_1486_ = v_breaks_1498_;
v___y_1487_ = v_numRegularExits_1501_;
v___y_1488_ = v_continues_1499_;
v___y_1489_ = v___x_1511_;
goto v___jp_1484_;
}
}
else
{
size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_usize_of_nat(v___x_1507_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1505_, v___x_1504_, v___x_1512_, v_reassigns_1502_);
lean_dec_ref(v___x_1505_);
v___y_1485_ = v_returnsEarly_1500_;
v___y_1486_ = v_breaks_1498_;
v___y_1487_ = v_numRegularExits_1501_;
v___y_1488_ = v_continues_1499_;
v___y_1489_ = v___x_1513_;
goto v___jp_1484_;
}
}
}
v___jp_1514_:
{
if (lean_obj_tag(v_body_x3f_1476_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1493_ = v_otherwise_1516_;
v___y_1494_ = v___y_1515_;
v_body_1495_ = v___x_1523_;
goto v___jp_1492_;
}
else
{
lean_object* v_val_1524_; lean_object* v___x_1525_; 
v_val_1524_ = lean_ctor_get(v_body_x3f_1476_, 0);
lean_inc(v_val_1524_);
lean_dec_ref(v_body_x3f_1476_);
v___x_1525_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1524_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
v___y_1493_ = v_otherwise_1516_;
v___y_1494_ = v___y_1515_;
v_body_1495_ = v_a_1526_;
goto v___jp_1492_;
}
else
{
lean_dec_ref(v_otherwise_1516_);
lean_dec_ref(v___y_1515_);
lean_dec_ref(v_reassigned_1473_);
return v___x_1525_;
}
}
}
v___jp_1527_:
{
if (lean_obj_tag(v_otherwise_x3f_1475_) == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1515_ = v_rhs_1528_;
v_otherwise_1516_ = v___x_1535_;
v___y_1517_ = v___y_1529_;
v___y_1518_ = v___y_1530_;
v___y_1519_ = v___y_1531_;
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1534_;
goto v___jp_1514_;
}
else
{
lean_object* v_val_1536_; lean_object* v___x_1537_; 
v_val_1536_ = lean_ctor_get(v_otherwise_x3f_1475_, 0);
lean_inc(v_val_1536_);
lean_dec_ref(v_otherwise_x3f_1475_);
v___x_1537_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1536_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v___x_1537_);
v___y_1515_ = v_rhs_1528_;
v_otherwise_1516_ = v_a_1538_;
v___y_1517_ = v___y_1529_;
v___y_1518_ = v___y_1530_;
v___y_1519_ = v___y_1531_;
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1534_;
goto v___jp_1514_;
}
else
{
lean_dec_ref(v_rhs_1528_);
lean_dec(v_body_x3f_1476_);
lean_dec_ref(v_reassigned_1473_);
return v___x_1537_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1645_, lean_object* v_decl_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v_reassigns_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1646_);
v___x_1683_ = l_Lean_Syntax_isOfKind(v_decl_1646_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1646_);
v___x_1685_ = l_Lean_Syntax_isOfKind(v_decl_1646_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1686_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1687_ = lean_box(0);
v___x_1688_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1687_, v___x_1685_);
v___x_1689_ = l_Std_Format_defWidth;
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = l_Std_Format_pretty(v___x_1688_, v___x_1689_, v___x_1690_, v___x_1690_);
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1686_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1693_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v_pattern_1696_; lean_object* v___y_1698_; lean_object* v_otherwise_x3f_1699_; lean_object* v_body_x3f_x3f_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v_body_x3f_x3f_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___x_1730_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v_pattern_1696_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1695_);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1769_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1730_);
v___x_1770_ = l_Lean_Syntax_isNone(v___x_1769_);
if (v___x_1770_ == 0)
{
uint8_t v___x_1771_; 
lean_inc(v___x_1769_);
v___x_1771_ = l_Lean_Syntax_matchesNull(v___x_1769_, v___x_1730_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v___x_1769_);
lean_dec(v_pattern_1696_);
v___x_1772_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1773_ = lean_box(0);
v___x_1774_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1773_, v___x_1771_);
v___x_1775_ = l_Std_Format_defWidth;
v___x_1776_ = l_Std_Format_pretty(v___x_1774_, v___x_1775_, v___x_1695_, v___x_1695_);
v___x_1777_ = l_Lean_stringToMessageData(v___x_1776_);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1772_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1778_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = l_Lean_Syntax_getArg(v___x_1769_, v___x_1695_);
lean_dec(v___x_1769_);
v___x_1781_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1782_ = l_Lean_Syntax_isOfKind(v___x_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_pattern_1696_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1784_ = lean_box(0);
v___x_1785_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1784_, v___x_1782_);
v___x_1786_ = l_Std_Format_defWidth;
v___x_1787_ = l_Std_Format_pretty(v___x_1785_, v___x_1786_, v___x_1695_, v___x_1695_);
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1783_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1789_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1790_;
}
else
{
v___y_1732_ = v_a_1647_;
v___y_1733_ = v_a_1648_;
v___y_1734_ = v_a_1649_;
v___y_1735_ = v_a_1650_;
v___y_1736_ = v_a_1651_;
v___y_1737_ = v_a_1652_;
goto v___jp_1731_;
}
}
}
else
{
lean_dec(v___x_1769_);
v___y_1732_ = v_a_1647_;
v___y_1733_ = v_a_1648_;
v___y_1734_ = v_a_1649_;
v___y_1735_ = v_a_1650_;
v___y_1736_ = v_a_1651_;
v___y_1737_ = v_a_1652_;
goto v___jp_1731_;
}
v___jp_1697_:
{
if (v_reassignment_1645_ == 0)
{
lean_object* v___x_1707_; 
lean_dec(v_pattern_1696_);
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1667_ = v_body_x3f_x3f_1700_;
v___y_1668_ = v___y_1698_;
v___y_1669_ = v_otherwise_x3f_1699_;
v_reassigns_1670_ = v___x_1707_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___y_1703_;
v___y_1674_ = v___y_1704_;
v___y_1675_ = v___y_1705_;
v___y_1676_ = v___y_1706_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1696_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v___y_1667_ = v_body_x3f_x3f_1700_;
v___y_1668_ = v___y_1698_;
v___y_1669_ = v_otherwise_x3f_1699_;
v_reassigns_1670_ = v_a_1709_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___y_1703_;
v___y_1674_ = v___y_1704_;
v___y_1675_ = v___y_1705_;
v___y_1676_ = v___y_1706_;
goto v___jp_1666_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_body_x3f_x3f_1700_);
lean_dec(v_otherwise_x3f_1699_);
lean_dec(v___y_1698_);
v_a_1710_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1708_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
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
v___jp_1718_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___y_1719_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_body_x3f_x3f_1721_);
v___y_1698_ = v___y_1720_;
v_otherwise_x3f_1699_ = v___x_1728_;
v_body_x3f_x3f_1700_ = v___x_1729_;
v___y_1701_ = v___y_1722_;
v___y_1702_ = v___y_1723_;
v___y_1703_ = v___y_1724_;
v___y_1704_ = v___y_1725_;
v___y_1705_ = v___y_1726_;
v___y_1706_ = v___y_1727_;
goto v___jp_1697_;
}
v___jp_1731_:
{
lean_object* v___x_1738_; lean_object* v_rhs_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1738_ = lean_unsigned_to_nat(3u);
v_rhs_1739_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1738_);
v___x_1740_ = lean_unsigned_to_nat(4u);
v___x_1741_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1740_);
v___x_1742_ = l_Lean_Syntax_isNone(v___x_1741_);
if (v___x_1742_ == 0)
{
uint8_t v___x_1743_; 
lean_inc(v___x_1741_);
v___x_1743_ = l_Lean_Syntax_matchesNull(v___x_1741_, v___x_1738_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1741_);
lean_dec(v_rhs_1739_);
lean_dec(v_pattern_1696_);
v___x_1744_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1745_ = lean_box(0);
v___x_1746_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1745_, v___x_1743_);
v___x_1747_ = l_Std_Format_defWidth;
v___x_1748_ = l_Std_Format_pretty(v___x_1746_, v___x_1747_, v___x_1695_, v___x_1695_);
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1744_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1750_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v_otherwise_x3f_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1752_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1753_ = l_Lean_Syntax_getArg(v___x_1741_, v___x_1730_);
v___x_1754_ = l_Lean_Syntax_getArg(v___x_1741_, v___x_1752_);
lean_dec(v___x_1741_);
v___x_1755_ = l_Lean_Syntax_isNone(v___x_1754_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; 
lean_inc(v___x_1754_);
v___x_1756_ = l_Lean_Syntax_matchesNull(v___x_1754_, v___x_1730_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v___x_1754_);
lean_dec(v_otherwise_x3f_1753_);
lean_dec(v_rhs_1739_);
lean_dec(v_pattern_1696_);
v___x_1757_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1758_, v___x_1756_);
v___x_1760_ = l_Std_Format_defWidth;
v___x_1761_ = l_Std_Format_pretty(v___x_1759_, v___x_1760_, v___x_1695_, v___x_1695_);
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1757_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1763_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1764_;
}
else
{
lean_object* v_body_x3f_x3f_1765_; lean_object* v___x_1766_; 
lean_dec(v_decl_1646_);
v_body_x3f_x3f_1765_ = l_Lean_Syntax_getArg(v___x_1754_, v___x_1695_);
lean_dec(v___x_1754_);
v___x_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_body_x3f_x3f_1765_);
v___y_1719_ = v_otherwise_x3f_1753_;
v___y_1720_ = v_rhs_1739_;
v_body_x3f_x3f_1721_ = v___x_1766_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___y_1734_;
v___y_1725_ = v___y_1735_;
v___y_1726_ = v___y_1736_;
v___y_1727_ = v___y_1737_;
goto v___jp_1718_;
}
}
else
{
lean_object* v___x_1767_; 
lean_dec(v___x_1754_);
lean_dec(v_decl_1646_);
v___x_1767_ = lean_box(0);
v___y_1719_ = v_otherwise_x3f_1753_;
v___y_1720_ = v_rhs_1739_;
v_body_x3f_x3f_1721_ = v___x_1767_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___y_1734_;
v___y_1725_ = v___y_1735_;
v___y_1726_ = v___y_1736_;
v___y_1727_ = v___y_1737_;
goto v___jp_1718_;
}
}
}
else
{
lean_object* v___x_1768_; 
lean_dec(v___x_1741_);
lean_dec(v_decl_1646_);
v___x_1768_ = lean_box(0);
v___y_1698_ = v_rhs_1739_;
v_otherwise_x3f_1699_ = v___x_1768_;
v_body_x3f_x3f_1700_ = v___x_1768_;
v___y_1701_ = v___y_1732_;
v___y_1702_ = v___y_1733_;
v___y_1703_ = v___y_1734_;
v___y_1704_ = v___y_1735_;
v___y_1705_ = v___y_1736_;
v___y_1706_ = v___y_1737_;
goto v___jp_1697_;
}
}
}
}
else
{
lean_object* v___x_1791_; lean_object* v_x_1792_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v_x_1792_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1791_);
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1792_);
v___x_1807_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v_x_1792_);
v___x_1808_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1809_, v___x_1807_);
v___x_1811_ = l_Std_Format_defWidth;
v___x_1812_ = l_Std_Format_pretty(v___x_1810_, v___x_1811_, v___x_1791_, v___x_1791_);
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1808_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1814_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1816_);
v___x_1818_ = l_Lean_Syntax_isNone(v___x_1817_);
if (v___x_1818_ == 0)
{
uint8_t v___x_1819_; 
lean_inc(v___x_1817_);
v___x_1819_ = l_Lean_Syntax_matchesNull(v___x_1817_, v___x_1816_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v___x_1817_);
lean_dec(v_x_1792_);
v___x_1820_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1821_ = lean_box(0);
v___x_1822_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1821_, v___x_1819_);
v___x_1823_ = l_Std_Format_defWidth;
v___x_1824_ = l_Std_Format_pretty(v___x_1822_, v___x_1823_, v___x_1791_, v___x_1791_);
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1820_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1826_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1828_ = l_Lean_Syntax_getArg(v___x_1817_, v___x_1791_);
lean_dec(v___x_1817_);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1830_ = l_Lean_Syntax_isOfKind(v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_x_1792_);
v___x_1831_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_Syntax_formatStx(v_decl_1646_, v___x_1832_, v___x_1830_);
v___x_1834_ = l_Std_Format_defWidth;
v___x_1835_ = l_Std_Format_pretty(v___x_1833_, v___x_1834_, v___x_1791_, v___x_1791_);
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1831_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1837_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1838_;
}
else
{
v___y_1794_ = v_a_1647_;
v___y_1795_ = v_a_1648_;
v___y_1796_ = v_a_1649_;
v___y_1797_ = v_a_1650_;
v___y_1798_ = v_a_1651_;
v___y_1799_ = v_a_1652_;
goto v___jp_1793_;
}
}
}
else
{
lean_dec(v___x_1817_);
v___y_1794_ = v_a_1647_;
v___y_1795_ = v_a_1648_;
v___y_1796_ = v_a_1649_;
v___y_1797_ = v_a_1650_;
v___y_1798_ = v_a_1651_;
v___y_1799_ = v_a_1652_;
goto v___jp_1793_;
}
}
v___jp_1793_:
{
lean_object* v___x_1800_; lean_object* v_rhs_1801_; 
v___x_1800_ = lean_unsigned_to_nat(3u);
v_rhs_1801_ = l_Lean_Syntax_getArg(v_decl_1646_, v___x_1800_);
lean_dec(v_decl_1646_);
if (v_reassignment_1645_ == 0)
{
lean_object* v___x_1802_; 
lean_dec(v_x_1792_);
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1655_ = v___y_1798_;
v___y_1656_ = v___y_1796_;
v___y_1657_ = v___y_1795_;
v___y_1658_ = v___y_1794_;
v___y_1659_ = v___y_1797_;
v___y_1660_ = v___y_1799_;
v___y_1661_ = v_rhs_1801_;
v___y_1662_ = v___x_1802_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1803_);
v___x_1805_ = lean_array_push(v___x_1804_, v_x_1792_);
v___y_1655_ = v___y_1798_;
v___y_1656_ = v___y_1796_;
v___y_1657_ = v___y_1795_;
v___y_1658_ = v___y_1794_;
v___y_1659_ = v___y_1797_;
v___y_1660_ = v___y_1799_;
v___y_1661_ = v_rhs_1801_;
v___y_1662_ = v___x_1805_;
goto v___jp_1654_;
}
}
}
v___jp_1654_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1661_);
v___x_1664_ = lean_box(0);
v___x_1665_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1662_, v___x_1663_, v___x_1664_, v___x_1664_, v___y_1658_, v___y_1657_, v___y_1656_, v___y_1659_, v___y_1655_, v___y_1660_);
return v___x_1665_;
}
v___jp_1666_:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1668_);
if (lean_obj_tag(v___y_1667_) == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_box(0);
v___x_1679_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1670_, v___x_1677_, v___y_1669_, v___x_1678_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1679_;
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1681_; 
v_val_1680_ = lean_ctor_get(v___y_1667_, 0);
lean_inc(v_val_1680_);
lean_dec_ref(v___y_1667_);
v___x_1681_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1670_, v___x_1677_, v___y_1669_, v_val_1680_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1941_, size_t v_sz_1942_, size_t v_i_1943_, lean_object* v_b_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_usize_dec_lt(v_i_1943_, v_sz_1942_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_b_1944_);
return v___x_1953_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1955_; 
v_a_1954_ = lean_array_uget_borrowed(v_as_1941_, v_i_1943_);
lean_inc(v_a_1954_);
v___x_1955_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1954_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; size_t v___x_1958_; size_t v___x_1959_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref(v___x_1955_);
v___x_1957_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1956_, v_b_1944_);
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_add(v_i_1943_, v___x_1958_);
v_i_1943_ = v___x_1959_;
v_b_1944_ = v___x_1957_;
goto _start;
}
else
{
lean_dec_ref(v_b_1944_);
return v___x_1955_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_1990_, lean_object* v_as_1991_, size_t v_sz_1992_, size_t v_i_1993_, lean_object* v_b_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_a_2003_; uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_1993_, v_sz_1992_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_1994_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v_a_2010_; uint8_t v___x_2011_; 
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2010_ = lean_array_uget_borrowed(v_as_1991_, v_i_1993_);
lean_inc(v_a_2010_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v_a_2010_, v___x_2009_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref(v___x_2012_);
v_a_2003_ = v_b_1994_;
goto v___jp_2002_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_b_1994_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___y_2024_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2021_ = lean_unsigned_to_nat(1u);
v___x_2022_ = lean_unsigned_to_nat(3u);
v___x_2041_ = l_Lean_Syntax_getArg(v_a_2010_, v___x_2021_);
v___x_2042_ = l_Lean_Syntax_getArgs(v___x_2041_);
lean_dec(v___x_2041_);
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2045_ = lean_array_get_size(v___x_2042_);
v___x_2046_ = lean_nat_dec_lt(v___x_2043_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_dec_ref(v___x_2042_);
v___y_2024_ = v___x_2044_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2047_ = lean_box(v___x_2011_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v___x_2044_);
v___x_2049_ = lean_nat_dec_le(v___x_2045_, v___x_2045_);
if (v___x_2049_ == 0)
{
if (v___x_2046_ == 0)
{
lean_dec_ref(v___x_2048_);
lean_dec_ref(v___x_2042_);
v___y_2024_ = v___x_2044_;
goto v___jp_2023_;
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; lean_object* v_snd_2053_; 
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2045_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2011_, v___x_1990_, v___x_2042_, v___x_2050_, v___x_2051_, v___x_2048_);
lean_dec_ref(v___x_2042_);
v_snd_2053_ = lean_ctor_get(v___x_2052_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2052_);
v___y_2024_ = v_snd_2053_;
goto v___jp_2023_;
}
}
else
{
size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; lean_object* v_snd_2057_; 
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = lean_usize_of_nat(v___x_2045_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2011_, v___x_1990_, v___x_2042_, v___x_2054_, v___x_2055_, v___x_2048_);
lean_dec_ref(v___x_2042_);
v_snd_2057_ = lean_ctor_get(v___x_2056_, 1);
lean_inc(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v___y_2024_ = v_snd_2057_;
goto v___jp_2023_;
}
}
v___jp_2023_:
{
size_t v_sz_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v_sz_2025_ = lean_array_size(v___y_2024_);
v___x_2026_ = ((size_t)0ULL);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2025_, v___x_2026_, v___y_2024_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_dec_ref(v___x_2028_);
v_a_2003_ = v_b_1994_;
goto v___jp_2002_;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v_b_1994_);
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec_ref(v___x_2027_);
v___x_2037_ = l_Lean_Syntax_getArg(v_a_2010_, v___x_2022_);
v___x_2038_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2037_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2038_);
v___x_2040_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_1994_, v_a_2039_);
v_a_2003_ = v___x_2040_;
goto v___jp_2002_;
}
else
{
lean_dec_ref(v_b_1994_);
return v___x_2038_;
}
}
}
}
}
v___jp_2002_:
{
size_t v___x_2004_; size_t v___x_2005_; 
v___x_2004_ = ((size_t)1ULL);
v___x_2005_ = lean_usize_add(v_i_1993_, v___x_2004_);
v_i_1993_ = v___x_2005_;
v_b_1994_ = v_a_2003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_a_2070_; uint8_t v___x_2074_; 
v___x_2074_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_b_2061_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v_a_2077_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v_a_2077_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2077_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v_a_2077_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2077_);
v___x_2093_ = l_Lean_Syntax_isOfKind(v_a_2077_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2094_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2095_ = lean_box(0);
lean_inc(v_a_2077_);
v___x_2096_ = l_Lean_Syntax_formatStx(v_a_2077_, v___x_2095_, v___x_2093_);
v___x_2097_ = l_Std_Format_defWidth;
v___x_2098_ = l_Std_Format_pretty(v___x_2096_, v___x_2097_, v___x_2076_, v___x_2076_);
v___x_2099_ = l_Lean_stringToMessageData(v___x_2098_);
v___x_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2094_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2100_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_dec_ref(v___x_2101_);
v_a_2070_ = v_b_2061_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v_b_2061_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = l_Lean_Syntax_getArg(v_a_2077_, v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2111_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec(v___x_2111_);
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2115_ = lean_box(0);
lean_inc(v_a_2077_);
v___x_2116_ = l_Lean_Syntax_formatStx(v_a_2077_, v___x_2115_, v___x_2113_);
v___x_2117_ = l_Std_Format_defWidth;
v___x_2118_ = l_Std_Format_pretty(v___x_2116_, v___x_2117_, v___x_2076_, v___x_2076_);
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2114_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2120_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_dec_ref(v___x_2121_);
v_a_2070_ = v_b_2061_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_b_2061_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2130_ = l_Lean_Syntax_getArg(v___x_2111_, v___x_2076_);
lean_dec(v___x_2111_);
v___x_2131_ = l_Lean_Syntax_getArgs(v___x_2130_);
lean_dec(v___x_2130_);
v_sz_2132_ = lean_array_size(v___x_2131_);
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2091_, v___x_2131_, v_sz_2132_, v___x_2133_, v_b_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec_ref(v___x_2131_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v_a_2070_ = v_a_2135_;
goto v___jp_2069_;
}
else
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2136_ = lean_unsigned_to_nat(2u);
v___x_2137_ = l_Lean_Syntax_getArg(v_a_2077_, v___x_2136_);
v___x_2138_ = l_Lean_Syntax_isNone(v___x_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
v___x_2139_ = l_Lean_Syntax_matchesNull(v___x_2137_, v___x_2136_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2141_ = lean_box(0);
lean_inc(v_a_2077_);
v___x_2142_ = l_Lean_Syntax_formatStx(v_a_2077_, v___x_2141_, v___x_2139_);
v___x_2143_ = l_Std_Format_defWidth;
v___x_2144_ = l_Std_Format_pretty(v___x_2142_, v___x_2143_, v___x_2076_, v___x_2076_);
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2140_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2146_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_dec_ref(v___x_2147_);
v_a_2070_ = v_b_2061_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_b_2061_);
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
v___y_2079_ = v___y_2062_;
v___y_2080_ = v___y_2063_;
v___y_2081_ = v___y_2064_;
v___y_2082_ = v___y_2065_;
v___y_2083_ = v___y_2066_;
v___y_2084_ = v___y_2067_;
goto v___jp_2078_;
}
}
else
{
lean_dec(v___x_2137_);
v___y_2079_ = v___y_2062_;
v___y_2080_ = v___y_2063_;
v___y_2081_ = v___y_2064_;
v___y_2082_ = v___y_2065_;
v___y_2083_ = v___y_2066_;
v___y_2084_ = v___y_2067_;
goto v___jp_2078_;
}
}
v___jp_2078_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_unsigned_to_nat(4u);
v___x_2086_ = l_Lean_Syntax_getArg(v_a_2077_, v___x_2085_);
v___x_2087_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2086_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2088_, v_b_2061_);
v_a_2070_ = v___x_2089_;
goto v___jp_2069_;
}
else
{
lean_dec_ref(v_b_2061_);
return v___x_2087_;
}
}
}
v___jp_2069_:
{
size_t v___x_2071_; size_t v___x_2072_; 
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2060_, v___x_2071_);
v_i_2060_ = v___x_2072_;
v_b_2061_ = v_a_2070_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2156_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
else
{
lean_object* v_val_2166_; lean_object* v___x_2167_; 
v_val_2166_ = lean_ctor_get(v_stx_x3f_2156_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_stx_x3f_2156_);
v___x_2167_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2166_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2174_, lean_object* v_as_2175_, size_t v_sz_2176_, size_t v_i_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_a_2187_; uint8_t v___x_2191_; 
v___x_2191_ = lean_usize_dec_lt(v_i_2177_, v_sz_2176_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_b_2178_);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v_a_2194_; uint8_t v___x_2195_; 
v___x_2193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2194_ = lean_array_uget_borrowed(v_as_2175_, v_i_2177_);
lean_inc(v_a_2194_);
v___x_2195_ = l_Lean_Syntax_isOfKind(v_a_2194_, v___x_2193_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_dec_ref(v___x_2196_);
v_a_2187_ = v_b_2178_;
goto v___jp_2186_;
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_b_2178_);
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___y_2208_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_unsigned_to_nat(3u);
v___x_2225_ = l_Lean_Syntax_getArg(v_a_2194_, v___x_2205_);
v___x_2226_ = l_Lean_Syntax_getArgs(v___x_2225_);
lean_dec(v___x_2225_);
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2229_ = lean_array_get_size(v___x_2226_);
v___x_2230_ = lean_nat_dec_lt(v___x_2227_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v___x_2226_);
v___y_2208_ = v___x_2228_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2231_ = lean_box(v___x_2195_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2228_);
v___x_2233_ = lean_nat_dec_le(v___x_2229_, v___x_2229_);
if (v___x_2233_ == 0)
{
if (v___x_2230_ == 0)
{
lean_dec_ref(v___x_2232_);
lean_dec_ref(v___x_2226_);
v___y_2208_ = v___x_2228_;
goto v___jp_2207_;
}
else
{
size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; lean_object* v_snd_2237_; 
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_usize_of_nat(v___x_2229_);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2195_, v___x_2174_, v___x_2226_, v___x_2234_, v___x_2235_, v___x_2232_);
lean_dec_ref(v___x_2226_);
v_snd_2237_ = lean_ctor_get(v___x_2236_, 1);
lean_inc(v_snd_2237_);
lean_dec_ref(v___x_2236_);
v___y_2208_ = v_snd_2237_;
goto v___jp_2207_;
}
}
else
{
size_t v___x_2238_; size_t v___x_2239_; lean_object* v___x_2240_; lean_object* v_snd_2241_; 
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = lean_usize_of_nat(v___x_2229_);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2195_, v___x_2174_, v___x_2226_, v___x_2238_, v___x_2239_, v___x_2232_);
lean_dec_ref(v___x_2226_);
v_snd_2241_ = lean_ctor_get(v___x_2240_, 1);
lean_inc(v_snd_2241_);
lean_dec_ref(v___x_2240_);
v___y_2208_ = v_snd_2241_;
goto v___jp_2207_;
}
}
v___jp_2207_:
{
size_t v_sz_2209_; size_t v___x_2210_; lean_object* v___x_2211_; 
v_sz_2209_ = lean_array_size(v___y_2208_);
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2209_, v___x_2210_, v___y_2208_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_dec_ref(v___x_2212_);
v_a_2187_ = v_b_2178_;
goto v___jp_2186_;
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v_b_2178_);
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v___x_2211_);
v___x_2221_ = l_Lean_Syntax_getArg(v_a_2194_, v___x_2206_);
v___x_2222_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2221_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2178_, v_a_2223_);
v_a_2187_ = v___x_2224_;
goto v___jp_2186_;
}
else
{
lean_dec_ref(v_b_2178_);
return v___x_2222_;
}
}
}
}
}
v___jp_2186_:
{
size_t v___x_2188_; size_t v___x_2189_; 
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2177_, v___x_2188_);
v_i_2177_ = v___x_2189_;
v_b_2178_ = v_a_2187_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2278_ = l_Lean_NameSet_empty;
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = 0;
v___x_2281_ = 1;
v___x_2282_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2282_, 0, v___x_2279_);
lean_ctor_set(v___x_2282_, 1, v___x_2278_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*2, v___x_2281_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*2 + 1, v___x_2280_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*2 + 2, v___x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2305_; lean_object* v_bodyInfo_2306_; lean_object* v___y_2310_; lean_object* v_bodyInfo_2311_; lean_object* v___x_2314_; lean_object* v_env_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_st_ref_get(v_a_2289_);
v_env_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_ref(v_env_2315_);
lean_dec(v___x_2314_);
lean_inc(v_stx_2283_);
v___x_2316_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2316_, 0, v_env_2315_);
lean_closure_set(v___x_2316_, 1, v_stx_2283_);
v___x_2317_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2316_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_4343_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_4343_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_4343_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
if (lean_obj_tag(v_a_2318_) == 1)
{
lean_object* v_val_2322_; lean_object* v_snd_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_del_object(v___x_2320_);
lean_dec(v_stx_2283_);
v_val_2322_ = lean_ctor_get(v_a_2318_, 0);
lean_inc(v_val_2322_);
lean_dec_ref(v_a_2318_);
v_snd_2323_ = lean_ctor_get(v_val_2322_, 1);
lean_inc(v_snd_2323_);
lean_dec(v_val_2322_);
v___x_2324_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2324_, 0, lean_box(0));
lean_closure_set(v___x_2324_, 1, v_snd_2323_);
v___x_2325_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2324_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v_stx_2283_ = v_a_2326_;
goto _start;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_a_2328_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2325_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2325_);
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
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___x_2518_; uint8_t v___x_2519_; uint8_t v___x_2520_; 
lean_dec(v_a_2318_);
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2283_);
v___x_2519_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2518_);
v___x_2520_ = 1;
if (v___x_2519_ == 0)
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2283_);
v___x_2522_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2283_);
v___x_2524_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2283_);
v___x_2526_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2283_);
v___x_2528_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2283_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
lean_del_object(v___x_2320_);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2283_);
v___x_2532_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2283_);
v___x_2534_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; uint8_t v___x_2536_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; 
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2283_);
v___x_2536_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2283_);
v___x_2598_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2283_);
v___x_2600_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2283_);
v___x_2602_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2283_);
v___x_2604_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2283_);
v___x_2606_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2283_);
v___x_2608_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2283_);
v___x_2610_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2283_);
v___x_2612_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2283_);
v___x_2614_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2283_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51));
lean_inc(v_stx_2283_);
v___x_2618_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2619_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53));
lean_inc(v_stx_2283_);
v___x_2620_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55));
lean_inc(v_stx_2283_);
v___x_2622_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57));
lean_inc(v_stx_2283_);
v___x_2624_ = l_Lean_Syntax_isOfKind(v_stx_2283_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v_env_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2625_ = lean_st_ref_get(v_a_2289_);
v_env_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_env_2626_);
lean_dec(v___x_2625_);
lean_inc_n(v_stx_2283_, 2);
v___x_2627_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2628_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2629_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2628_, v_env_2626_, v___x_2627_);
v___x_2630_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2631_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2629_, v___x_2630_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2662_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2662_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2662_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_fst_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2660_; 
v_fst_2636_ = lean_ctor_get(v_a_2632_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_a_2632_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v_a_2632_, 1);
lean_dec(v_unused_2661_);
v___x_2638_ = v_a_2632_;
v_isShared_2639_ = v_isSharedCheck_2660_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_fst_2636_);
lean_dec(v_a_2632_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2660_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
if (lean_obj_tag(v_fst_2636_) == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_del_object(v___x_2634_);
v___x_2640_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2641_ = l_Lean_MessageData_ofName(v___x_2627_);
lean_inc_ref(v___x_2641_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set_tag(v___x_2638_, 7);
lean_ctor_set(v___x_2638_, 1, v___x_2641_);
lean_ctor_set(v___x_2638_, 0, v___x_2640_);
v___x_2643_ = v___x_2638_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2644_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2647_ = l_Lean_indentD(v___x_2646_);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2645_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
lean_ctor_set(v___x_2651_, 1, v___x_2641_);
v___x_2652_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2653_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2654_;
}
}
else
{
lean_object* v_val_2656_; lean_object* v___x_2658_; 
lean_del_object(v___x_2638_);
lean_dec(v___x_2627_);
lean_dec(v_stx_2283_);
v_val_2656_ = lean_ctor_get(v_fst_2636_, 0);
lean_inc(v_val_2656_);
lean_dec_ref(v_fst_2636_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_val_2656_);
v___x_2658_ = v___x_2634_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_val_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v___x_2627_);
lean_dec(v_stx_2283_);
v_a_2663_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2631_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2631_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___y_2675_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_unsigned_to_nat(5u);
v___x_2673_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2672_);
v___x_2684_ = lean_unsigned_to_nat(6u);
v___x_2685_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2684_);
lean_dec(v_stx_2283_);
v___x_2686_ = l_Lean_Syntax_getOptional_x3f(v___x_2685_);
lean_dec(v___x_2685_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_box(0);
v___y_2675_ = v___x_2687_;
goto v___jp_2674_;
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_val_2688_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2686_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_val_2688_);
lean_dec(v___x_2686_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_val_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v___y_2675_ = v___x_2693_;
goto v___jp_2674_;
}
}
}
v___jp_2674_:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2673_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2676_) == 0)
{
if (lean_obj_tag(v___y_2675_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Lean_NameSet_empty;
v___x_2679_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2679_, 0, v___x_2671_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*2, v___x_2622_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*2 + 1, v___x_2622_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*2 + 2, v___x_2622_);
v___y_2310_ = v_a_2677_;
v_bodyInfo_2311_ = v___x_2679_;
goto v___jp_2309_;
}
else
{
lean_object* v_a_2680_; lean_object* v_val_2681_; lean_object* v___x_2682_; 
v_a_2680_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2676_);
v_val_2681_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_val_2681_);
lean_dec_ref(v___y_2675_);
v___x_2682_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2681_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref(v___x_2682_);
v___y_2310_ = v_a_2680_;
v_bodyInfo_2311_ = v_a_2683_;
goto v___jp_2309_;
}
else
{
lean_dec(v_a_2680_);
return v___x_2682_;
}
}
}
else
{
lean_dec(v___y_2675_);
return v___x_2676_;
}
}
}
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___y_2700_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_unsigned_to_nat(5u);
v___x_2698_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2697_);
v___x_2709_ = lean_unsigned_to_nat(6u);
v___x_2710_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2709_);
lean_dec(v_stx_2283_);
v___x_2711_ = l_Lean_Syntax_getOptional_x3f(v___x_2710_);
lean_dec(v___x_2710_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_box(0);
v___y_2700_ = v___x_2712_;
goto v___jp_2699_;
}
else
{
lean_object* v_val_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_val_2713_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2711_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_val_2713_);
lean_dec(v___x_2711_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_val_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
v___y_2700_ = v___x_2718_;
goto v___jp_2699_;
}
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2698_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2701_) == 0)
{
if (lean_obj_tag(v___y_2700_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v___x_2703_ = l_Lean_NameSet_empty;
v___x_2704_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2704_, 0, v___x_2696_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*2, v___x_2620_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*2 + 1, v___x_2620_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*2 + 2, v___x_2620_);
v___y_2305_ = v_a_2702_;
v_bodyInfo_2306_ = v___x_2704_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2705_; lean_object* v_val_2706_; lean_object* v___x_2707_; 
v_a_2705_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2701_);
v_val_2706_ = lean_ctor_get(v___y_2700_, 0);
lean_inc(v_val_2706_);
lean_dec_ref(v___y_2700_);
v___x_2707_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2706_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref(v___x_2707_);
v___y_2305_ = v_a_2705_;
v_bodyInfo_2306_ = v_a_2708_;
goto v___jp_2304_;
}
else
{
lean_dec(v_a_2705_);
return v___x_2707_;
}
}
}
else
{
lean_dec(v___y_2700_);
return v___x_2701_;
}
}
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2721_ = lean_unsigned_to_nat(0u);
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2936_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2722_);
v___x_2937_ = l_Lean_Syntax_isNone(v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = lean_unsigned_to_nat(5u);
v___x_2939_ = l_Lean_Syntax_matchesNull(v___x_2936_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v_env_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2940_ = lean_st_ref_get(v_a_2289_);
v_env_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc_ref(v_env_2941_);
lean_dec(v___x_2940_);
lean_inc_n(v_stx_2283_, 2);
v___x_2942_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2943_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2944_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2943_, v_env_2941_, v___x_2942_);
v___x_2945_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2946_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2944_, v___x_2945_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2977_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2977_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2977_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_fst_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2975_; 
v_fst_2951_ = lean_ctor_get(v_a_2947_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v_a_2947_, 1);
lean_dec(v_unused_2976_);
v___x_2953_ = v_a_2947_;
v_isShared_2954_ = v_isSharedCheck_2975_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_fst_2951_);
lean_dec(v_a_2947_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2975_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
if (lean_obj_tag(v_fst_2951_) == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
lean_del_object(v___x_2949_);
v___x_2955_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2956_ = l_Lean_MessageData_ofName(v___x_2942_);
lean_inc_ref(v___x_2956_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 7);
lean_ctor_set(v___x_2953_, 1, v___x_2956_);
lean_ctor_set(v___x_2953_, 0, v___x_2955_);
v___x_2958_ = v___x_2953_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2959_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2962_ = l_Lean_indentD(v___x_2961_);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2960_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___x_2956_);
v___x_2967_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2968_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2969_;
}
}
else
{
lean_object* v_val_2971_; lean_object* v___x_2973_; 
lean_del_object(v___x_2953_);
lean_dec(v___x_2942_);
lean_dec(v_stx_2283_);
v_val_2971_ = lean_ctor_get(v_fst_2951_, 0);
lean_inc(v_val_2971_);
lean_dec_ref(v_fst_2951_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v_val_2971_);
v___x_2973_ = v___x_2949_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_val_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v___x_2942_);
lean_dec(v_stx_2283_);
v_a_2978_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2946_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2946_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
v___y_2724_ = v_a_2284_;
v___y_2725_ = v_a_2285_;
v___y_2726_ = v_a_2286_;
v___y_2727_ = v_a_2287_;
v___y_2728_ = v_a_2288_;
v___y_2729_ = v_a_2289_;
goto v___jp_2723_;
}
}
else
{
lean_dec(v___x_2936_);
v___y_2724_ = v_a_2284_;
v___y_2725_ = v_a_2285_;
v___y_2726_ = v_a_2286_;
v___y_2727_ = v_a_2287_;
v___y_2728_ = v_a_2288_;
v___y_2729_ = v_a_2289_;
goto v___jp_2723_;
}
v___jp_2723_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2730_ = lean_unsigned_to_nat(4u);
v___x_2731_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2730_);
v___x_2732_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59));
lean_inc(v___x_2731_);
v___x_2733_ = l_Lean_Syntax_isOfKind(v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v_env_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec(v___x_2731_);
v___x_2734_ = lean_st_ref_get(v___y_2729_);
v_env_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc_ref(v_env_2735_);
lean_dec(v___x_2734_);
lean_inc_n(v_stx_2283_, 2);
v___x_2736_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2737_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2738_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2737_, v_env_2735_, v___x_2736_);
v___x_2739_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2740_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2738_, v___x_2739_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2771_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2771_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2771_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_fst_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2769_; 
v_fst_2745_ = lean_ctor_get(v_a_2741_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_a_2741_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v_a_2741_, 1);
lean_dec(v_unused_2770_);
v___x_2747_ = v_a_2741_;
v_isShared_2748_ = v_isSharedCheck_2769_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_fst_2745_);
lean_dec(v_a_2741_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2769_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
if (lean_obj_tag(v_fst_2745_) == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_del_object(v___x_2743_);
v___x_2749_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2750_ = l_Lean_MessageData_ofName(v___x_2736_);
lean_inc_ref(v___x_2750_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 7);
lean_ctor_set(v___x_2747_, 1, v___x_2750_);
lean_ctor_set(v___x_2747_, 0, v___x_2749_);
v___x_2752_ = v___x_2747_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2753_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2756_ = l_Lean_indentD(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2754_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___x_2750_);
v___x_2761_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2762_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2763_;
}
}
else
{
lean_object* v_val_2765_; lean_object* v___x_2767_; 
lean_del_object(v___x_2747_);
lean_dec(v___x_2736_);
lean_dec(v_stx_2283_);
v_val_2765_ = lean_ctor_get(v_fst_2745_, 0);
lean_inc(v_val_2765_);
lean_dec_ref(v_fst_2745_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_val_2765_);
v___x_2767_ = v___x_2743_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_val_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v___x_2736_);
lean_dec(v_stx_2283_);
v_a_2772_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2740_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2740_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; size_t v_sz_2782_; size_t v___x_2783_; lean_object* v___x_2784_; 
v___x_2780_ = l_Lean_Syntax_getArg(v___x_2731_, v___x_2721_);
v___x_2781_ = l_Lean_Syntax_getArgs(v___x_2780_);
lean_dec(v___x_2780_);
v_sz_2782_ = lean_array_size(v___x_2781_);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2782_, v___x_2783_, v___x_2781_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v___x_2785_; lean_object* v_env_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v___x_2731_);
v___x_2785_ = lean_st_ref_get(v___y_2729_);
v_env_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_ref(v_env_2786_);
lean_dec(v___x_2785_);
lean_inc_n(v_stx_2283_, 2);
v___x_2787_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2788_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2789_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2788_, v_env_2786_, v___x_2787_);
v___x_2790_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2791_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2789_, v___x_2790_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2822_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v_fst_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2820_; 
v_fst_2796_ = lean_ctor_get(v_a_2792_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_a_2792_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v_a_2792_, 1);
lean_dec(v_unused_2821_);
v___x_2798_ = v_a_2792_;
v_isShared_2799_ = v_isSharedCheck_2820_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_fst_2796_);
lean_dec(v_a_2792_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2820_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
if (lean_obj_tag(v_fst_2796_) == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2803_; 
lean_del_object(v___x_2794_);
v___x_2800_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2801_ = l_Lean_MessageData_ofName(v___x_2787_);
lean_inc_ref(v___x_2801_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 7);
lean_ctor_set(v___x_2798_, 1, v___x_2801_);
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2803_ = v___x_2798_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2804_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2807_ = l_Lean_indentD(v___x_2806_);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2805_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
lean_ctor_set(v___x_2811_, 1, v___x_2801_);
v___x_2812_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2813_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2814_;
}
}
else
{
lean_object* v_val_2816_; lean_object* v___x_2818_; 
lean_del_object(v___x_2798_);
lean_dec(v___x_2787_);
lean_dec(v_stx_2283_);
v_val_2816_ = lean_ctor_get(v_fst_2796_, 0);
lean_inc(v_val_2816_);
lean_dec_ref(v_fst_2796_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_val_2816_);
v___x_2818_ = v___x_2794_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_val_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v___x_2787_);
lean_dec(v_stx_2283_);
v_a_2823_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2791_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2791_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_val_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v_val_2831_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2831_);
lean_dec_ref(v___x_2784_);
v___x_2832_ = l_Lean_Syntax_getArg(v___x_2731_, v___x_2722_);
lean_dec(v___x_2731_);
v___x_2833_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61));
lean_inc(v___x_2832_);
v___x_2834_ = l_Lean_Syntax_isOfKind(v___x_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v_env_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec(v___x_2832_);
lean_dec(v_val_2831_);
v___x_2835_ = lean_st_ref_get(v___y_2729_);
v_env_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_env_2836_);
lean_dec(v___x_2835_);
lean_inc_n(v_stx_2283_, 2);
v___x_2837_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2838_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2839_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2838_, v_env_2836_, v___x_2837_);
v___x_2840_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2841_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2839_, v___x_2840_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2872_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2872_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2872_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_fst_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2870_; 
v_fst_2846_ = lean_ctor_get(v_a_2842_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2842_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v_a_2842_, 1);
lean_dec(v_unused_2871_);
v___x_2848_ = v_a_2842_;
v_isShared_2849_ = v_isSharedCheck_2870_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_fst_2846_);
lean_dec(v_a_2842_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2870_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
if (lean_obj_tag(v_fst_2846_) == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_del_object(v___x_2844_);
v___x_2850_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2851_ = l_Lean_MessageData_ofName(v___x_2837_);
lean_inc_ref(v___x_2851_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set_tag(v___x_2848_, 7);
lean_ctor_set(v___x_2848_, 1, v___x_2851_);
lean_ctor_set(v___x_2848_, 0, v___x_2850_);
v___x_2853_ = v___x_2848_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2854_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2857_ = l_Lean_indentD(v___x_2856_);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2855_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___x_2851_);
v___x_2862_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2863_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2864_;
}
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2868_; 
lean_del_object(v___x_2848_);
lean_dec(v___x_2837_);
lean_dec(v_stx_2283_);
v_val_2866_ = lean_ctor_get(v_fst_2846_, 0);
lean_inc(v_val_2866_);
lean_dec_ref(v_fst_2846_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_val_2866_);
v___x_2868_ = v___x_2844_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_val_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v___x_2837_);
lean_dec(v_stx_2283_);
v_a_2873_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2841_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2841_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2881_ = l_Lean_Syntax_getArg(v___x_2832_, v___x_2722_);
v___x_2882_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
v___x_2883_ = l_Lean_Syntax_isOfKind(v___x_2881_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v_env_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec(v___x_2832_);
lean_dec(v_val_2831_);
v___x_2884_ = lean_st_ref_get(v___y_2729_);
v_env_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_env_2885_);
lean_dec(v___x_2884_);
lean_inc_n(v_stx_2283_, 2);
v___x_2886_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2887_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2888_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2887_, v_env_2885_, v___x_2886_);
v___x_2889_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2890_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2888_, v___x_2889_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2921_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2921_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2921_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_fst_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2919_; 
v_fst_2895_ = lean_ctor_get(v_a_2891_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_a_2891_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_a_2891_, 1);
lean_dec(v_unused_2920_);
v___x_2897_ = v_a_2891_;
v_isShared_2898_ = v_isSharedCheck_2919_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_fst_2895_);
lean_dec(v_a_2891_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2919_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
if (lean_obj_tag(v_fst_2895_) == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_del_object(v___x_2893_);
v___x_2899_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2900_ = l_Lean_MessageData_ofName(v___x_2886_);
lean_inc_ref(v___x_2900_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set_tag(v___x_2897_, 7);
lean_ctor_set(v___x_2897_, 1, v___x_2900_);
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2902_ = v___x_2897_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2903_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2906_ = l_Lean_indentD(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2904_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2900_);
v___x_2911_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2912_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2913_;
}
}
else
{
lean_object* v_val_2915_; lean_object* v___x_2917_; 
lean_del_object(v___x_2897_);
lean_dec(v___x_2886_);
lean_dec(v_stx_2283_);
v_val_2915_ = lean_ctor_get(v_fst_2895_, 0);
lean_inc(v_val_2915_);
lean_dec_ref(v_fst_2895_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v_val_2915_);
v___x_2917_ = v___x_2893_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_val_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v___x_2886_);
lean_dec(v_stx_2283_);
v_a_2922_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2890_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2890_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_dec(v_stx_2283_);
v___x_2930_ = lean_unsigned_to_nat(3u);
v___x_2931_ = l_Lean_Syntax_getArg(v___x_2832_, v___x_2930_);
lean_dec(v___x_2832_);
v___x_2932_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2931_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; size_t v_sz_2934_; lean_object* v___x_2935_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v_sz_2934_ = lean_array_size(v_val_2831_);
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2831_, v_sz_2934_, v___x_2783_, v_a_2933_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v_val_2831_);
return v___x_2935_;
}
else
{
lean_dec(v_val_2831_);
return v___x_2932_;
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
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v_stx_2283_);
v___x_2986_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec(v_stx_2283_);
v___x_2988_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v_stx_2283_);
v___x_2990_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; size_t v_sz_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2992_ = lean_unsigned_to_nat(2u);
v___x_2993_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2992_);
v___x_2994_ = l_Lean_Syntax_getArgs(v___x_2993_);
lean_dec(v___x_2993_);
v_sz_2995_ = lean_array_size(v___x_2994_);
v___x_2996_ = ((size_t)0ULL);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_2995_, v___x_2996_, v___x_2994_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v___x_2998_; lean_object* v_env_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2998_ = lean_st_ref_get(v_a_2289_);
v_env_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc_ref(v_env_2999_);
lean_dec(v___x_2998_);
lean_inc_n(v_stx_2283_, 2);
v___x_3000_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3001_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3002_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3001_, v_env_2999_, v___x_3000_);
v___x_3003_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3004_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3002_, v___x_3003_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3035_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3035_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3035_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v_fst_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3033_; 
v_fst_3009_ = lean_ctor_get(v_a_3005_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_a_3005_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; 
v_unused_3034_ = lean_ctor_get(v_a_3005_, 1);
lean_dec(v_unused_3034_);
v___x_3011_ = v_a_3005_;
v_isShared_3012_ = v_isSharedCheck_3033_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_fst_3009_);
lean_dec(v_a_3005_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3033_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
if (lean_obj_tag(v_fst_3009_) == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
lean_del_object(v___x_3007_);
v___x_3013_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3014_ = l_Lean_MessageData_ofName(v___x_3000_);
lean_inc_ref(v___x_3014_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 7);
lean_ctor_set(v___x_3011_, 1, v___x_3014_);
lean_ctor_set(v___x_3011_, 0, v___x_3013_);
v___x_3016_ = v___x_3011_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3017_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3020_ = l_Lean_indentD(v___x_3019_);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3018_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___x_3014_);
v___x_3025_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3026_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3027_;
}
}
else
{
lean_object* v_val_3029_; lean_object* v___x_3031_; 
lean_del_object(v___x_3011_);
lean_dec(v___x_3000_);
lean_dec(v_stx_2283_);
v_val_3029_ = lean_ctor_get(v_fst_3009_, 0);
lean_inc(v_val_3029_);
lean_dec_ref(v_fst_3009_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v_val_3029_);
v___x_3031_ = v___x_3007_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_val_3029_);
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
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v___x_3000_);
lean_dec(v_stx_2283_);
v_a_3036_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3004_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3004_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_val_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3178_; 
v_val_3044_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3046_ = v___x_2997_;
v_isShared_3047_ = v_isSharedCheck_3178_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_val_3044_);
lean_dec(v___x_2997_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3178_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v_finSeq_x3f_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3048_ = lean_unsigned_to_nat(1u);
v___x_3049_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3048_);
v___x_3073_ = lean_unsigned_to_nat(3u);
v___x_3074_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3073_);
v___x_3075_ = l_Lean_Syntax_isNone(v___x_3074_);
if (v___x_3075_ == 0)
{
uint8_t v___x_3076_; 
lean_inc(v___x_3074_);
v___x_3076_ = l_Lean_Syntax_matchesNull(v___x_3074_, v___x_3048_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v_env_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_dec(v___x_3074_);
lean_dec(v___x_3049_);
lean_del_object(v___x_3046_);
lean_dec(v_val_3044_);
v___x_3077_ = lean_st_ref_get(v_a_2289_);
v_env_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3078_);
lean_dec(v___x_3077_);
lean_inc_n(v_stx_2283_, 2);
v___x_3079_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3080_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3081_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3080_, v_env_3078_, v___x_3079_);
v___x_3082_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3083_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3081_, v___x_3082_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3114_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3114_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3114_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v_fst_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3112_; 
v_fst_3088_ = lean_ctor_get(v_a_3084_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_a_3084_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v_a_3084_, 1);
lean_dec(v_unused_3113_);
v___x_3090_ = v_a_3084_;
v_isShared_3091_ = v_isSharedCheck_3112_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_fst_3088_);
lean_dec(v_a_3084_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3112_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
if (lean_obj_tag(v_fst_3088_) == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_del_object(v___x_3086_);
v___x_3092_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3093_ = l_Lean_MessageData_ofName(v___x_3079_);
lean_inc_ref(v___x_3093_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set_tag(v___x_3090_, 7);
lean_ctor_set(v___x_3090_, 1, v___x_3093_);
lean_ctor_set(v___x_3090_, 0, v___x_3092_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3096_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3099_ = l_Lean_indentD(v___x_3098_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3097_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3093_);
v___x_3104_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3105_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3106_;
}
}
else
{
lean_object* v_val_3108_; lean_object* v___x_3110_; 
lean_del_object(v___x_3090_);
lean_dec(v___x_3079_);
lean_dec(v_stx_2283_);
v_val_3108_ = lean_ctor_get(v_fst_3088_, 0);
lean_inc(v_val_3108_);
lean_dec_ref(v_fst_3088_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v_val_3108_);
v___x_3110_ = v___x_3086_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_val_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v___x_3079_);
lean_dec(v_stx_2283_);
v_a_3115_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3083_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3083_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = l_Lean_Syntax_getArg(v___x_3074_, v___x_3123_);
lean_dec(v___x_3074_);
v___x_3125_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65));
lean_inc(v___x_3124_);
v___x_3126_ = l_Lean_Syntax_isOfKind(v___x_3124_, v___x_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v_env_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v___x_3124_);
lean_dec(v___x_3049_);
lean_del_object(v___x_3046_);
lean_dec(v_val_3044_);
v___x_3127_ = lean_st_ref_get(v_a_2289_);
v_env_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc_ref(v_env_3128_);
lean_dec(v___x_3127_);
lean_inc_n(v_stx_2283_, 2);
v___x_3129_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3130_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3131_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3130_, v_env_3128_, v___x_3129_);
v___x_3132_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3133_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3131_, v___x_3132_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3164_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3164_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3164_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_fst_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3162_; 
v_fst_3138_ = lean_ctor_get(v_a_3134_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_a_3134_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; 
v_unused_3163_ = lean_ctor_get(v_a_3134_, 1);
lean_dec(v_unused_3163_);
v___x_3140_ = v_a_3134_;
v_isShared_3141_ = v_isSharedCheck_3162_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_fst_3138_);
lean_dec(v_a_3134_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3162_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
if (lean_obj_tag(v_fst_3138_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_del_object(v___x_3136_);
v___x_3142_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3143_ = l_Lean_MessageData_ofName(v___x_3129_);
lean_inc_ref(v___x_3143_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set_tag(v___x_3140_, 7);
lean_ctor_set(v___x_3140_, 1, v___x_3143_);
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3145_ = v___x_3140_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3149_ = l_Lean_indentD(v___x_3148_);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3147_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v___x_3143_);
v___x_3154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3153_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3155_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3156_;
}
}
else
{
lean_object* v_val_3158_; lean_object* v___x_3160_; 
lean_del_object(v___x_3140_);
lean_dec(v___x_3129_);
lean_dec(v_stx_2283_);
v_val_3158_ = lean_ctor_get(v_fst_3138_, 0);
lean_inc(v_val_3158_);
lean_dec_ref(v_fst_3138_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v_val_3158_);
v___x_3160_ = v___x_3136_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_val_3158_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v___x_3129_);
lean_dec(v_stx_2283_);
v_a_3165_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3133_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3133_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
lean_dec(v_stx_2283_);
v___x_3173_ = l_Lean_Syntax_getArg(v___x_3124_, v___x_3048_);
lean_dec(v___x_3124_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3173_);
v___x_3175_ = v___x_3046_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
v_finSeq_x3f_3051_ = v___x_3175_;
v___y_3052_ = v_a_2284_;
v___y_3053_ = v_a_2285_;
v___y_3054_ = v_a_2286_;
v___y_3055_ = v_a_2287_;
v___y_3056_ = v_a_2288_;
v___y_3057_ = v_a_2289_;
goto v___jp_3050_;
}
}
}
}
else
{
lean_object* v___x_3177_; 
lean_dec(v___x_3074_);
lean_del_object(v___x_3046_);
lean_dec(v_stx_2283_);
v___x_3177_ = lean_box(0);
v_finSeq_x3f_3051_ = v___x_3177_;
v___y_3052_ = v_a_2284_;
v___y_3053_ = v_a_2285_;
v___y_3054_ = v_a_2286_;
v___y_3055_ = v_a_2287_;
v___y_3056_ = v_a_2288_;
v___y_3057_ = v_a_2289_;
goto v___jp_3050_;
}
v___jp_3050_:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3049_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; size_t v_sz_3060_; lean_object* v___x_3061_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v_sz_3060_ = lean_array_size(v_val_3044_);
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3044_, v_sz_3060_, v___x_2996_, v_a_3059_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v_val_3044_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3063_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3072_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3062_, v_a_3064_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
else
{
lean_dec(v_a_3062_);
return v___x_3063_;
}
}
else
{
lean_dec(v_finSeq_x3f_3051_);
return v___x_3061_;
}
}
else
{
lean_dec(v_finSeq_x3f_3051_);
lean_dec(v_val_3044_);
return v___x_3058_;
}
}
}
}
}
}
else
{
lean_object* v___x_3179_; lean_object* v___y_3181_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3179_ = lean_unsigned_to_nat(1u);
v___x_3252_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3179_);
v___x_3253_ = l_Lean_Syntax_getArgs(v___x_3252_);
lean_dec(v___x_3252_);
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3256_ = lean_array_get_size(v___x_3253_);
v___x_3257_ = lean_nat_dec_lt(v___x_3254_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_dec_ref(v___x_3253_);
v___y_3181_ = v___x_3255_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3258_ = lean_box(v___x_2610_);
v___x_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
lean_ctor_set(v___x_3259_, 1, v___x_3255_);
v___x_3260_ = lean_nat_dec_le(v___x_3256_, v___x_3256_);
if (v___x_3260_ == 0)
{
if (v___x_3257_ == 0)
{
lean_dec_ref(v___x_3259_);
lean_dec_ref(v___x_3253_);
v___y_3181_ = v___x_3255_;
goto v___jp_3180_;
}
else
{
size_t v___x_3261_; size_t v___x_3262_; lean_object* v___x_3263_; lean_object* v_snd_3264_; 
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = lean_usize_of_nat(v___x_3256_);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2610_, v___x_2608_, v___x_3253_, v___x_3261_, v___x_3262_, v___x_3259_);
lean_dec_ref(v___x_3253_);
v_snd_3264_ = lean_ctor_get(v___x_3263_, 1);
lean_inc(v_snd_3264_);
lean_dec_ref(v___x_3263_);
v___y_3181_ = v_snd_3264_;
goto v___jp_3180_;
}
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; lean_object* v_snd_3268_; 
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = lean_usize_of_nat(v___x_3256_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2610_, v___x_2608_, v___x_3253_, v___x_3265_, v___x_3266_, v___x_3259_);
lean_dec_ref(v___x_3253_);
v_snd_3268_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_snd_3268_);
lean_dec_ref(v___x_3267_);
v___y_3181_ = v_snd_3268_;
goto v___jp_3180_;
}
}
v___jp_3180_:
{
size_t v_sz_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v_sz_3182_ = lean_array_size(v___y_3181_);
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3182_, v___x_3183_, v___y_3181_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v___x_3185_; lean_object* v_env_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3185_ = lean_st_ref_get(v_a_2289_);
v_env_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc_ref(v_env_3186_);
lean_dec(v___x_3185_);
lean_inc_n(v_stx_2283_, 2);
v___x_3187_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3188_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3189_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3188_, v_env_3186_, v___x_3187_);
v___x_3190_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3191_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3189_, v___x_3190_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3222_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3222_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3222_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v_fst_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3220_; 
v_fst_3196_ = lean_ctor_get(v_a_3192_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_a_3192_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_a_3192_, 1);
lean_dec(v_unused_3221_);
v___x_3198_ = v_a_3192_;
v_isShared_3199_ = v_isSharedCheck_3220_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_fst_3196_);
lean_dec(v_a_3192_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3220_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
if (lean_obj_tag(v_fst_3196_) == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_del_object(v___x_3194_);
v___x_3200_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3201_ = l_Lean_MessageData_ofName(v___x_3187_);
lean_inc_ref(v___x_3201_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 7);
lean_ctor_set(v___x_3198_, 1, v___x_3201_);
lean_ctor_set(v___x_3198_, 0, v___x_3200_);
v___x_3203_ = v___x_3198_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3204_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3207_ = l_Lean_indentD(v___x_3206_);
v___x_3208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3205_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3208_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v___x_3201_);
v___x_3212_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3213_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3214_;
}
}
else
{
lean_object* v_val_3216_; lean_object* v___x_3218_; 
lean_del_object(v___x_3198_);
lean_dec(v___x_3187_);
lean_dec(v_stx_2283_);
v_val_3216_ = lean_ctor_get(v_fst_3196_, 0);
lean_inc(v_val_3216_);
lean_dec_ref(v_fst_3196_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v_val_3216_);
v___x_3218_ = v___x_3194_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_val_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec(v___x_3187_);
lean_dec(v_stx_2283_);
v_a_3223_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3191_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3191_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
lean_dec_ref(v___x_3184_);
v___x_3231_ = lean_unsigned_to_nat(3u);
v___x_3232_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3231_);
lean_dec(v_stx_2283_);
v___x_3233_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3232_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3251_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3251_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3251_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
uint8_t v_returnsEarly_3238_; lean_object* v_reassigns_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3249_; 
v_returnsEarly_3238_ = lean_ctor_get_uint8(v_a_3234_, sizeof(void*)*2 + 2);
v_reassigns_3239_ = lean_ctor_get(v_a_3234_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_a_3234_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_a_3234_, 0);
lean_dec(v_unused_3250_);
v___x_3241_ = v_a_3234_;
v_isShared_3242_ = v_isSharedCheck_3249_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_reassigns_3239_);
lean_dec(v_a_3234_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3249_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3179_);
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_reassigns_3239_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, sizeof(void*)*2 + 2, v_returnsEarly_3238_);
v___x_3244_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3246_; 
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*2, v___x_2608_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*2 + 1, v___x_2608_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3244_);
v___x_3246_ = v___x_3236_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
else
{
return v___x_3233_;
}
}
}
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_unsigned_to_nat(3u);
v___x_3271_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3270_);
lean_dec(v_stx_2283_);
v___x_3272_ = l_Lean_NameSet_empty;
v___x_3273_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3273_, 0, v___x_3269_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*2, v___x_2606_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*2 + 1, v___x_2606_);
lean_ctor_set_uint8(v___x_3273_, sizeof(void*)*2 + 2, v___x_2606_);
v___x_3274_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3271_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3283_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3273_, v_a_3275_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_dec_ref(v___x_3273_);
return v___x_3274_;
}
}
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; size_t v_sz_3287_; size_t v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = lean_unsigned_to_nat(4u);
v___x_3285_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3284_);
v___x_3286_ = l_Lean_Syntax_getArgs(v___x_3285_);
lean_dec(v___x_3285_);
v_sz_3287_ = lean_array_size(v___x_3286_);
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3287_, v___x_3288_, v___x_3286_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; lean_object* v_env_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3290_ = lean_st_ref_get(v_a_2289_);
v_env_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc_ref(v_env_3291_);
lean_dec(v___x_3290_);
lean_inc_n(v_stx_2283_, 2);
v___x_3292_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3293_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3294_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3293_, v_env_3291_, v___x_3292_);
v___x_3295_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3296_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3294_, v___x_3295_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3327_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3327_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3327_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_fst_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3325_; 
v_fst_3301_ = lean_ctor_get(v_a_3297_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_a_3297_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; 
v_unused_3326_ = lean_ctor_get(v_a_3297_, 1);
lean_dec(v_unused_3326_);
v___x_3303_ = v_a_3297_;
v_isShared_3304_ = v_isSharedCheck_3325_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_fst_3301_);
lean_dec(v_a_3297_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3325_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
if (lean_obj_tag(v_fst_3301_) == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_del_object(v___x_3299_);
v___x_3305_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3306_ = l_Lean_MessageData_ofName(v___x_3292_);
lean_inc_ref(v___x_3306_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set_tag(v___x_3303_, 7);
lean_ctor_set(v___x_3303_, 1, v___x_3306_);
lean_ctor_set(v___x_3303_, 0, v___x_3305_);
v___x_3308_ = v___x_3303_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3309_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3312_ = l_Lean_indentD(v___x_3311_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3310_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
lean_ctor_set(v___x_3316_, 1, v___x_3306_);
v___x_3317_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3318_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3319_;
}
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3323_; 
lean_del_object(v___x_3303_);
lean_dec(v___x_3292_);
lean_dec(v_stx_2283_);
v_val_3321_ = lean_ctor_get(v_fst_3301_, 0);
lean_inc(v_val_3321_);
lean_dec_ref(v_fst_3301_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v_val_3321_);
v___x_3323_ = v___x_3299_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_val_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v___x_3292_);
lean_dec(v_stx_2283_);
v_a_3328_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3296_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3296_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_val_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3423_; 
v_val_3336_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3338_ = v___x_3289_;
v_isShared_3339_ = v_isSharedCheck_3423_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_val_3336_);
lean_dec(v___x_3289_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3423_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v_elseSeq_x3f_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3340_ = lean_unsigned_to_nat(3u);
v___x_3341_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3340_);
v___x_3366_ = lean_unsigned_to_nat(5u);
v___x_3367_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3366_);
v___x_3368_ = l_Lean_Syntax_isNone(v___x_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3367_);
v___x_3370_ = l_Lean_Syntax_matchesNull(v___x_3367_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v_env_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v___x_3367_);
lean_dec(v___x_3341_);
lean_del_object(v___x_3338_);
lean_dec(v_val_3336_);
v___x_3371_ = lean_st_ref_get(v_a_2289_);
v_env_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc_ref(v_env_3372_);
lean_dec(v___x_3371_);
lean_inc_n(v_stx_2283_, 2);
v___x_3373_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3374_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3375_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3374_, v_env_3372_, v___x_3373_);
v___x_3376_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3377_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3375_, v___x_3376_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3408_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3408_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3408_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v_fst_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3406_; 
v_fst_3382_ = lean_ctor_get(v_a_3378_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_a_3378_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_a_3378_, 1);
lean_dec(v_unused_3407_);
v___x_3384_ = v_a_3378_;
v_isShared_3385_ = v_isSharedCheck_3406_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_fst_3382_);
lean_dec(v_a_3378_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3406_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
if (lean_obj_tag(v_fst_3382_) == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
lean_del_object(v___x_3380_);
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3387_ = l_Lean_MessageData_ofName(v___x_3373_);
lean_inc_ref(v___x_3387_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 7);
lean_ctor_set(v___x_3384_, 1, v___x_3387_);
lean_ctor_set(v___x_3384_, 0, v___x_3386_);
v___x_3389_ = v___x_3384_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3390_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3393_ = l_Lean_indentD(v___x_3392_);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3391_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v___x_3387_);
v___x_3398_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3399_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3400_;
}
}
else
{
lean_object* v_val_3402_; lean_object* v___x_3404_; 
lean_del_object(v___x_3384_);
lean_dec(v___x_3373_);
lean_dec(v_stx_2283_);
v_val_3402_ = lean_ctor_get(v_fst_3382_, 0);
lean_inc(v_val_3402_);
lean_dec_ref(v_fst_3382_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v_val_3402_);
v___x_3404_ = v___x_3380_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_val_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v___x_3373_);
lean_dec(v_stx_2283_);
v_a_3409_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3377_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3377_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
lean_dec(v_stx_2283_);
v___x_3417_ = lean_unsigned_to_nat(1u);
v___x_3418_ = l_Lean_Syntax_getArg(v___x_3367_, v___x_3417_);
lean_dec(v___x_3367_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3418_);
v___x_3420_ = v___x_3338_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
v_elseSeq_x3f_3343_ = v___x_3420_;
v___y_3344_ = v_a_2284_;
v___y_3345_ = v_a_2285_;
v___y_3346_ = v_a_2286_;
v___y_3347_ = v_a_2287_;
v___y_3348_ = v_a_2288_;
v___y_3349_ = v_a_2289_;
goto v___jp_3342_;
}
}
}
else
{
lean_object* v___x_3422_; 
lean_dec(v___x_3367_);
lean_del_object(v___x_3338_);
lean_dec(v_stx_2283_);
v___x_3422_ = lean_box(0);
v_elseSeq_x3f_3343_ = v___x_3422_;
v___y_3344_ = v_a_2284_;
v___y_3345_ = v_a_2285_;
v___y_3346_ = v_a_2286_;
v___y_3347_ = v_a_2287_;
v___y_3348_ = v_a_2288_;
v___y_3349_ = v_a_2289_;
goto v___jp_3342_;
}
v___jp_3342_:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; size_t v_sz_3353_; lean_object* v___x_3354_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref(v___x_3350_);
v___x_3352_ = l_Array_reverse___redArg(v_val_3336_);
v_sz_3353_ = lean_array_size(v___x_3352_);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3352_, v_sz_3353_, v___x_3288_, v_a_3351_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___x_3352_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref(v___x_3354_);
v___x_3356_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3341_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3365_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3365_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3365_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3357_, v_a_3355_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3361_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
lean_dec(v_a_3355_);
return v___x_3356_;
}
}
else
{
lean_dec(v___x_3341_);
return v___x_3354_;
}
}
else
{
lean_dec(v___x_3341_);
lean_dec(v_val_3336_);
return v___x_3350_;
}
}
}
}
}
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3596_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3425_);
v___x_3597_ = l_Lean_Syntax_isNone(v___x_3596_);
if (v___x_3597_ == 0)
{
uint8_t v___x_3598_; 
lean_inc(v___x_3596_);
v___x_3598_ = l_Lean_Syntax_matchesNull(v___x_3596_, v___x_3425_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v_env_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
lean_dec(v___x_3596_);
v___x_3599_ = lean_st_ref_get(v_a_2289_);
v_env_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc_ref(v_env_3600_);
lean_dec(v___x_3599_);
lean_inc_n(v_stx_2283_, 2);
v___x_3601_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3602_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3603_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3602_, v_env_3600_, v___x_3601_);
v___x_3604_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3605_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3603_, v___x_3604_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3636_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3636_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3636_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v_fst_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3634_; 
v_fst_3610_ = lean_ctor_get(v_a_3606_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_a_3606_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; 
v_unused_3635_ = lean_ctor_get(v_a_3606_, 1);
lean_dec(v_unused_3635_);
v___x_3612_ = v_a_3606_;
v_isShared_3613_ = v_isSharedCheck_3634_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_fst_3610_);
lean_dec(v_a_3606_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3634_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
if (lean_obj_tag(v_fst_3610_) == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_del_object(v___x_3608_);
v___x_3614_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3615_ = l_Lean_MessageData_ofName(v___x_3601_);
lean_inc_ref(v___x_3615_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 7);
lean_ctor_set(v___x_3612_, 1, v___x_3615_);
lean_ctor_set(v___x_3612_, 0, v___x_3614_);
v___x_3617_ = v___x_3612_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3614_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3621_ = l_Lean_indentD(v___x_3620_);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3619_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v___x_3615_);
v___x_3626_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3627_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3628_;
}
}
else
{
lean_object* v_val_3630_; lean_object* v___x_3632_; 
lean_del_object(v___x_3612_);
lean_dec(v___x_3601_);
lean_dec(v_stx_2283_);
v_val_3630_ = lean_ctor_get(v_fst_3610_, 0);
lean_inc(v_val_3630_);
lean_dec_ref(v_fst_3610_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_val_3630_);
v___x_3632_ = v___x_3608_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_val_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v___x_3601_);
lean_dec(v_stx_2283_);
v_a_3637_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3605_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3605_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3645_ = l_Lean_Syntax_getArg(v___x_3596_, v___x_3424_);
lean_dec(v___x_3596_);
v___x_3646_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69));
v___x_3647_ = l_Lean_Syntax_isOfKind(v___x_3645_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v_env_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3648_ = lean_st_ref_get(v_a_2289_);
v_env_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc_ref(v_env_3649_);
lean_dec(v___x_3648_);
lean_inc_n(v_stx_2283_, 2);
v___x_3650_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3651_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3652_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3651_, v_env_3649_, v___x_3650_);
v___x_3653_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3654_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3652_, v___x_3653_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3685_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3685_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3685_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_fst_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3683_; 
v_fst_3659_ = lean_ctor_get(v_a_3655_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_a_3655_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v_a_3655_, 1);
lean_dec(v_unused_3684_);
v___x_3661_ = v_a_3655_;
v_isShared_3662_ = v_isSharedCheck_3683_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_fst_3659_);
lean_dec(v_a_3655_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3683_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
if (lean_obj_tag(v_fst_3659_) == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_del_object(v___x_3657_);
v___x_3663_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3664_ = l_Lean_MessageData_ofName(v___x_3650_);
lean_inc_ref(v___x_3664_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 7);
lean_ctor_set(v___x_3661_, 1, v___x_3664_);
lean_ctor_set(v___x_3661_, 0, v___x_3663_);
v___x_3666_ = v___x_3661_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3667_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3670_ = l_Lean_indentD(v___x_3669_);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3668_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v___x_3664_);
v___x_3675_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3676_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3677_;
}
}
else
{
lean_object* v_val_3679_; lean_object* v___x_3681_; 
lean_del_object(v___x_3661_);
lean_dec(v___x_3650_);
lean_dec(v_stx_2283_);
v_val_3679_ = lean_ctor_get(v_fst_3659_, 0);
lean_inc(v_val_3679_);
lean_dec_ref(v_fst_3659_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_val_3679_);
v___x_3681_ = v___x_3657_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_val_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v___x_3650_);
lean_dec(v_stx_2283_);
v_a_3686_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3654_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3654_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
v___y_3491_ = v_a_2284_;
v___y_3492_ = v_a_2285_;
v___y_3493_ = v_a_2286_;
v___y_3494_ = v_a_2287_;
v___y_3495_ = v_a_2288_;
v___y_3496_ = v_a_2289_;
goto v___jp_3490_;
}
}
}
else
{
lean_dec(v___x_3596_);
v___y_3491_ = v_a_2284_;
v___y_3492_ = v_a_2285_;
v___y_3493_ = v_a_2286_;
v___y_3494_ = v_a_2287_;
v___y_3495_ = v_a_2288_;
v___y_3496_ = v_a_2289_;
goto v___jp_3490_;
}
v___jp_3426_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3433_ = lean_unsigned_to_nat(6u);
v___x_3434_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3433_);
v___x_3435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3434_);
v___x_3436_ = l_Lean_Syntax_isOfKind(v___x_3434_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v_env_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec(v___x_3434_);
v___x_3437_ = lean_st_ref_get(v___y_3432_);
v_env_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc_ref(v_env_3438_);
lean_dec(v___x_3437_);
lean_inc_n(v_stx_2283_, 2);
v___x_3439_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3440_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3441_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3440_, v_env_3438_, v___x_3439_);
v___x_3442_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3443_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3441_, v___x_3442_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3474_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3474_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3474_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_fst_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3472_; 
v_fst_3448_ = lean_ctor_get(v_a_3444_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_a_3444_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v_a_3444_, 1);
lean_dec(v_unused_3473_);
v___x_3450_ = v_a_3444_;
v_isShared_3451_ = v_isSharedCheck_3472_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_fst_3448_);
lean_dec(v_a_3444_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3472_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
if (lean_obj_tag(v_fst_3448_) == 0)
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_del_object(v___x_3446_);
v___x_3452_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3453_ = l_Lean_MessageData_ofName(v___x_3439_);
lean_inc_ref(v___x_3453_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 7);
lean_ctor_set(v___x_3450_, 1, v___x_3453_);
lean_ctor_set(v___x_3450_, 0, v___x_3452_);
v___x_3455_ = v___x_3450_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3456_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3459_ = l_Lean_indentD(v___x_3458_);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3457_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v___x_3453_);
v___x_3464_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3465_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3466_;
}
}
else
{
lean_object* v_val_3468_; lean_object* v___x_3470_; 
lean_del_object(v___x_3450_);
lean_dec(v___x_3439_);
lean_dec(v_stx_2283_);
v_val_3468_ = lean_ctor_get(v_fst_3448_, 0);
lean_inc(v_val_3468_);
lean_dec_ref(v_fst_3448_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v_val_3468_);
v___x_3470_ = v___x_3446_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_val_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v___x_3439_);
lean_dec(v_stx_2283_);
v_a_3475_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3443_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3443_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; size_t v_sz_3487_; size_t v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v_stx_2283_);
v___x_3483_ = l_Lean_Syntax_getArg(v___x_3434_, v___x_3424_);
lean_dec(v___x_3434_);
v___x_3484_ = l_Lean_Syntax_getArgs(v___x_3483_);
lean_dec(v___x_3483_);
v___x_3485_ = l_Lean_NameSet_empty;
v___x_3486_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3486_, 0, v___x_3425_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*2, v___x_2602_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*2 + 1, v___x_2602_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*2 + 2, v___x_2602_);
v_sz_3487_ = lean_array_size(v___x_3484_);
v___x_3488_ = ((size_t)0ULL);
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2602_, v___x_3484_, v_sz_3487_, v___x_3488_, v___x_3486_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec_ref(v___x_3484_);
return v___x_3489_;
}
}
v___jp_3490_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3497_ = lean_unsigned_to_nat(2u);
v___x_3498_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3497_);
v___x_3499_ = l_Lean_Syntax_isNone(v___x_3498_);
if (v___x_3499_ == 0)
{
uint8_t v___x_3500_; 
lean_inc(v___x_3498_);
v___x_3500_ = l_Lean_Syntax_matchesNull(v___x_3498_, v___x_3425_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v_env_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec(v___x_3498_);
v___x_3501_ = lean_st_ref_get(v___y_3496_);
v_env_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc_ref(v_env_3502_);
lean_dec(v___x_3501_);
lean_inc_n(v_stx_2283_, 2);
v___x_3503_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3504_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3505_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3504_, v_env_3502_, v___x_3503_);
v___x_3506_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3507_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3505_, v___x_3506_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3538_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3538_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3538_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_fst_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3536_; 
v_fst_3512_ = lean_ctor_get(v_a_3508_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_a_3508_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v_a_3508_, 1);
lean_dec(v_unused_3537_);
v___x_3514_ = v_a_3508_;
v_isShared_3515_ = v_isSharedCheck_3536_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_fst_3512_);
lean_dec(v_a_3508_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3536_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
if (lean_obj_tag(v_fst_3512_) == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_del_object(v___x_3510_);
v___x_3516_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3517_ = l_Lean_MessageData_ofName(v___x_3503_);
lean_inc_ref(v___x_3517_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 7);
lean_ctor_set(v___x_3514_, 1, v___x_3517_);
lean_ctor_set(v___x_3514_, 0, v___x_3516_);
v___x_3519_ = v___x_3514_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3520_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3523_ = l_Lean_indentD(v___x_3522_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3521_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___x_3517_);
v___x_3528_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3529_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3530_;
}
}
else
{
lean_object* v_val_3532_; lean_object* v___x_3534_; 
lean_del_object(v___x_3514_);
lean_dec(v___x_3503_);
lean_dec(v_stx_2283_);
v_val_3532_ = lean_ctor_get(v_fst_3512_, 0);
lean_inc(v_val_3532_);
lean_dec_ref(v_fst_3512_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v_val_3532_);
v___x_3534_ = v___x_3510_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_val_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v___x_3503_);
lean_dec(v_stx_2283_);
v_a_3539_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3507_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3507_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3547_ = l_Lean_Syntax_getArg(v___x_3498_, v___x_3424_);
lean_dec(v___x_3498_);
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67));
v___x_3549_ = l_Lean_Syntax_isOfKind(v___x_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v_env_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3550_ = lean_st_ref_get(v___y_3496_);
v_env_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc_ref(v_env_3551_);
lean_dec(v___x_3550_);
lean_inc_n(v_stx_2283_, 2);
v___x_3552_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3553_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3554_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3553_, v_env_3551_, v___x_3552_);
v___x_3555_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3556_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3554_, v___x_3555_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3587_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3587_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3587_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v_fst_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3585_; 
v_fst_3561_ = lean_ctor_get(v_a_3557_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3557_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v_a_3557_, 1);
lean_dec(v_unused_3586_);
v___x_3563_ = v_a_3557_;
v_isShared_3564_ = v_isSharedCheck_3585_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_fst_3561_);
lean_dec(v_a_3557_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3585_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
if (lean_obj_tag(v_fst_3561_) == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3568_; 
lean_del_object(v___x_3559_);
v___x_3565_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3566_ = l_Lean_MessageData_ofName(v___x_3552_);
lean_inc_ref(v___x_3566_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 7);
lean_ctor_set(v___x_3563_, 1, v___x_3566_);
lean_ctor_set(v___x_3563_, 0, v___x_3565_);
v___x_3568_ = v___x_3563_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3572_ = l_Lean_indentD(v___x_3571_);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3570_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v___x_3566_);
v___x_3577_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3578_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3579_;
}
}
else
{
lean_object* v_val_3581_; lean_object* v___x_3583_; 
lean_del_object(v___x_3563_);
lean_dec(v___x_3552_);
lean_dec(v_stx_2283_);
v_val_3581_ = lean_ctor_get(v_fst_3561_, 0);
lean_inc(v_val_3581_);
lean_dec_ref(v_fst_3561_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v_val_3581_);
v___x_3583_ = v___x_3559_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_val_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___x_3552_);
lean_dec(v_stx_2283_);
v_a_3588_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3556_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3556_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
v___y_3427_ = v___y_3491_;
v___y_3428_ = v___y_3492_;
v___y_3429_ = v___y_3493_;
v___y_3430_ = v___y_3494_;
v___y_3431_ = v___y_3495_;
v___y_3432_ = v___y_3496_;
goto v___jp_3426_;
}
}
}
else
{
lean_dec(v___x_3498_);
v___y_3427_ = v___y_3491_;
v___y_3428_ = v___y_3492_;
v___y_3429_ = v___y_3493_;
v___y_3430_ = v___y_3494_;
v___y_3431_ = v___y_3495_;
v___y_3432_ = v___y_3496_;
goto v___jp_3426_;
}
}
}
}
else
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; 
v___x_3694_ = lean_unsigned_to_nat(0u);
v___x_3695_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3694_);
v___x_3696_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3695_);
v___x_3697_ = l_Lean_Syntax_isOfKind(v___x_3695_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3695_);
v___x_3699_ = l_Lean_Syntax_isOfKind(v___x_3695_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v_env_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_dec(v___x_3695_);
v___x_3700_ = lean_st_ref_get(v_a_2289_);
v_env_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc_ref(v_env_3701_);
lean_dec(v___x_3700_);
lean_inc_n(v_stx_2283_, 2);
v___x_3702_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3703_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3704_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3703_, v_env_3701_, v___x_3702_);
v___x_3705_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3706_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3704_, v___x_3705_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3737_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3737_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3737_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v_fst_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3735_; 
v_fst_3711_ = lean_ctor_get(v_a_3707_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_a_3707_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v_a_3707_, 1);
lean_dec(v_unused_3736_);
v___x_3713_ = v_a_3707_;
v_isShared_3714_ = v_isSharedCheck_3735_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_fst_3711_);
lean_dec(v_a_3707_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3735_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
if (lean_obj_tag(v_fst_3711_) == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_del_object(v___x_3709_);
v___x_3715_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3716_ = l_Lean_MessageData_ofName(v___x_3702_);
lean_inc_ref(v___x_3716_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set_tag(v___x_3713_, 7);
lean_ctor_set(v___x_3713_, 1, v___x_3716_);
lean_ctor_set(v___x_3713_, 0, v___x_3715_);
v___x_3718_ = v___x_3713_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3719_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3722_ = l_Lean_indentD(v___x_3721_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3720_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v___x_3716_);
v___x_3727_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3728_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3729_;
}
}
else
{
lean_object* v_val_3731_; lean_object* v___x_3733_; 
lean_del_object(v___x_3713_);
lean_dec(v___x_3702_);
lean_dec(v_stx_2283_);
v_val_3731_ = lean_ctor_get(v_fst_3711_, 0);
lean_inc(v_val_3731_);
lean_dec_ref(v_fst_3711_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v_val_3731_);
v___x_3733_ = v___x_3709_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_val_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v___x_3702_);
lean_dec(v_stx_2283_);
v_a_3738_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3706_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3706_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v___x_3746_; 
lean_dec(v_stx_2283_);
v___x_3746_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2520_, v___x_3695_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3746_;
}
}
else
{
lean_object* v___x_3747_; 
lean_dec(v_stx_2283_);
v___x_3747_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2520_, v___x_3695_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3747_;
}
}
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3748_ = lean_unsigned_to_nat(0u);
v___x_3749_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3748_);
v___x_3750_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71));
lean_inc(v___x_3749_);
v___x_3751_ = l_Lean_Syntax_isOfKind(v___x_3749_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73));
lean_inc(v___x_3749_);
v___x_3753_ = l_Lean_Syntax_isOfKind(v___x_3749_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v_env_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec(v___x_3749_);
v___x_3754_ = lean_st_ref_get(v_a_2289_);
v_env_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc_ref(v_env_3755_);
lean_dec(v___x_3754_);
lean_inc_n(v_stx_2283_, 2);
v___x_3756_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3757_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3758_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3757_, v_env_3755_, v___x_3756_);
v___x_3759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3760_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3758_, v___x_3759_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3791_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3791_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3791_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_fst_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3789_; 
v_fst_3765_ = lean_ctor_get(v_a_3761_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_a_3761_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; 
v_unused_3790_ = lean_ctor_get(v_a_3761_, 1);
lean_dec(v_unused_3790_);
v___x_3767_ = v_a_3761_;
v_isShared_3768_ = v_isSharedCheck_3789_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_fst_3765_);
lean_dec(v_a_3761_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3789_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
if (lean_obj_tag(v_fst_3765_) == 0)
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
lean_del_object(v___x_3763_);
v___x_3769_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3770_ = l_Lean_MessageData_ofName(v___x_3756_);
lean_inc_ref(v___x_3770_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 7);
lean_ctor_set(v___x_3767_, 1, v___x_3770_);
lean_ctor_set(v___x_3767_, 0, v___x_3769_);
v___x_3772_ = v___x_3767_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3773_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3776_ = l_Lean_indentD(v___x_3775_);
v___x_3777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3774_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set(v___x_3780_, 1, v___x_3770_);
v___x_3781_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3782_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3783_;
}
}
else
{
lean_object* v_val_3785_; lean_object* v___x_3787_; 
lean_del_object(v___x_3767_);
lean_dec(v___x_3756_);
lean_dec(v_stx_2283_);
v_val_3785_ = lean_ctor_get(v_fst_3765_, 0);
lean_inc(v_val_3785_);
lean_dec_ref(v_fst_3765_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v_val_3785_);
v___x_3787_ = v___x_3763_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_val_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v___x_3756_);
lean_dec(v_stx_2283_);
v_a_3792_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3760_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3760_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v___x_3800_; 
lean_dec(v_stx_2283_);
v___x_3800_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3749_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v___x_3749_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref(v___x_3800_);
v___x_3802_ = lean_box(0);
v___x_3803_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3801_, v___x_3802_, v___x_3802_, v___x_3802_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3803_;
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
v_a_3804_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3800_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3800_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
else
{
lean_object* v___x_3812_; 
lean_dec(v_stx_2283_);
v___x_3812_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3749_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v___x_3749_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3812_);
v___x_3814_ = lean_box(0);
v___x_3815_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3813_, v___x_3814_, v___x_3814_, v___x_3814_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3815_;
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3812_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3812_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3824_ = lean_unsigned_to_nat(1u);
v___x_3825_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3824_);
v___x_3826_ = l_Lean_Syntax_isNone(v___x_3825_);
if (v___x_3826_ == 0)
{
uint8_t v___x_3827_; 
v___x_3827_ = l_Lean_Syntax_matchesNull(v___x_3825_, v___x_3824_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; lean_object* v_env_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3828_ = lean_st_ref_get(v_a_2289_);
v_env_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc_ref(v_env_3829_);
lean_dec(v___x_3828_);
lean_inc_n(v_stx_2283_, 2);
v___x_3830_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3831_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3832_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3831_, v_env_3829_, v___x_3830_);
v___x_3833_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3834_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3832_, v___x_3833_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3865_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3865_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3865_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_fst_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3863_; 
v_fst_3839_ = lean_ctor_get(v_a_3835_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_a_3835_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; 
v_unused_3864_ = lean_ctor_get(v_a_3835_, 1);
lean_dec(v_unused_3864_);
v___x_3841_ = v_a_3835_;
v_isShared_3842_ = v_isSharedCheck_3863_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_fst_3839_);
lean_dec(v_a_3835_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3863_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
if (lean_obj_tag(v_fst_3839_) == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3846_; 
lean_del_object(v___x_3837_);
v___x_3843_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3844_ = l_Lean_MessageData_ofName(v___x_3830_);
lean_inc_ref(v___x_3844_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set_tag(v___x_3841_, 7);
lean_ctor_set(v___x_3841_, 1, v___x_3844_);
lean_ctor_set(v___x_3841_, 0, v___x_3843_);
v___x_3846_ = v___x_3841_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3847_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3850_ = l_Lean_indentD(v___x_3849_);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3848_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set(v___x_3854_, 1, v___x_3844_);
v___x_3855_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3856_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3857_;
}
}
else
{
lean_object* v_val_3859_; lean_object* v___x_3861_; 
lean_del_object(v___x_3841_);
lean_dec(v___x_3830_);
lean_dec(v_stx_2283_);
v_val_3859_ = lean_ctor_get(v_fst_3839_, 0);
lean_inc(v_val_3859_);
lean_dec_ref(v_fst_3839_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_val_3859_);
v___x_3861_ = v___x_3837_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_val_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v___x_3830_);
lean_dec(v_stx_2283_);
v_a_3866_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3834_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3834_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
v___y_2538_ = v_a_2284_;
v___y_2539_ = v_a_2285_;
v___y_2540_ = v_a_2286_;
v___y_2541_ = v_a_2287_;
v___y_2542_ = v_a_2288_;
v___y_2543_ = v_a_2289_;
goto v___jp_2537_;
}
}
else
{
lean_dec(v___x_3825_);
v___y_2538_ = v_a_2284_;
v___y_2539_ = v_a_2285_;
v___y_2540_ = v_a_2286_;
v___y_2541_ = v_a_2287_;
v___y_2542_ = v_a_2288_;
v___y_2543_ = v_a_2289_;
goto v___jp_2537_;
}
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; 
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3875_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3874_);
v___x_3876_ = l_Lean_Syntax_isNone(v___x_3875_);
if (v___x_3876_ == 0)
{
uint8_t v___x_3877_; 
v___x_3877_ = l_Lean_Syntax_matchesNull(v___x_3875_, v___x_3874_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v_env_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3878_ = lean_st_ref_get(v_a_2289_);
v_env_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc_ref(v_env_3879_);
lean_dec(v___x_3878_);
lean_inc_n(v_stx_2283_, 2);
v___x_3880_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3881_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3882_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3881_, v_env_3879_, v___x_3880_);
v___x_3883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3884_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3882_, v___x_3883_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3915_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3915_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3915_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v_fst_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3913_; 
v_fst_3889_ = lean_ctor_get(v_a_3885_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_a_3885_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v_a_3885_, 1);
lean_dec(v_unused_3914_);
v___x_3891_ = v_a_3885_;
v_isShared_3892_ = v_isSharedCheck_3913_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_fst_3889_);
lean_dec(v_a_3885_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3913_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
if (lean_obj_tag(v_fst_3889_) == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_del_object(v___x_3887_);
v___x_3893_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3894_ = l_Lean_MessageData_ofName(v___x_3880_);
lean_inc_ref(v___x_3894_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 7);
lean_ctor_set(v___x_3891_, 1, v___x_3894_);
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3896_ = v___x_3891_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3897_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3900_ = l_Lean_indentD(v___x_3899_);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3898_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3901_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
lean_ctor_set(v___x_3904_, 1, v___x_3894_);
v___x_3905_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3904_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3906_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3907_;
}
}
else
{
lean_object* v_val_3909_; lean_object* v___x_3911_; 
lean_del_object(v___x_3891_);
lean_dec(v___x_3880_);
lean_dec(v_stx_2283_);
v_val_3909_ = lean_ctor_get(v_fst_3889_, 0);
lean_inc(v_val_3909_);
lean_dec_ref(v_fst_3889_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v_val_3909_);
v___x_3911_ = v___x_3887_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_val_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v___x_3880_);
lean_dec(v_stx_2283_);
v_a_3916_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3884_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3884_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
v___y_2337_ = v_a_2284_;
v___y_2338_ = v_a_2285_;
v___y_2339_ = v_a_2286_;
v___y_2340_ = v_a_2287_;
v___y_2341_ = v_a_2288_;
v___y_2342_ = v_a_2289_;
goto v___jp_2336_;
}
}
else
{
lean_dec(v___x_3875_);
v___y_2337_ = v_a_2284_;
v___y_2338_ = v_a_2285_;
v___y_2339_ = v_a_2286_;
v___y_2340_ = v_a_2287_;
v___y_2341_ = v_a_2288_;
v___y_2342_ = v_a_2289_;
goto v___jp_2336_;
}
}
v___jp_2537_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2544_ = lean_unsigned_to_nat(2u);
v___x_2545_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2547_ = l_Lean_Syntax_isOfKind(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v_env_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2548_ = lean_st_ref_get(v___y_2543_);
v_env_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc_ref(v_env_2549_);
lean_dec(v___x_2548_);
lean_inc_n(v_stx_2283_, 2);
v___x_2550_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2551_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2552_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2551_, v_env_2549_, v___x_2550_);
v___x_2553_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2554_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2552_, v___x_2553_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2585_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2585_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2585_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_fst_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2583_; 
v_fst_2559_ = lean_ctor_get(v_a_2555_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v_a_2555_, 1);
lean_dec(v_unused_2584_);
v___x_2561_ = v_a_2555_;
v_isShared_2562_ = v_isSharedCheck_2583_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_fst_2559_);
lean_dec(v_a_2555_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2583_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
if (lean_obj_tag(v_fst_2559_) == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_del_object(v___x_2557_);
v___x_2563_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2564_ = l_Lean_MessageData_ofName(v___x_2550_);
lean_inc_ref(v___x_2564_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 7);
lean_ctor_set(v___x_2561_, 1, v___x_2564_);
lean_ctor_set(v___x_2561_, 0, v___x_2563_);
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2567_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2570_ = l_Lean_indentD(v___x_2569_);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2568_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v___x_2564_);
v___x_2575_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2576_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v___x_2577_;
}
}
else
{
lean_object* v_val_2579_; lean_object* v___x_2581_; 
lean_del_object(v___x_2561_);
lean_dec(v___x_2550_);
lean_dec(v_stx_2283_);
v_val_2579_ = lean_ctor_get(v_fst_2559_, 0);
lean_inc(v_val_2579_);
lean_dec_ref(v_fst_2559_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_val_2579_);
v___x_2581_ = v___x_2557_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_val_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v___x_2550_);
lean_dec(v_stx_2283_);
v_a_2586_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2554_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2554_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_unsigned_to_nat(3u);
v___x_2595_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2594_);
lean_dec(v_stx_2283_);
v___x_2596_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2536_, v___x_2595_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v___x_2596_;
}
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3924_);
v___x_3926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3927_ = l_Lean_Syntax_isOfKind(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; lean_object* v_env_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3928_ = lean_st_ref_get(v_a_2289_);
v_env_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc_ref(v_env_3929_);
lean_dec(v___x_3928_);
lean_inc_n(v_stx_2283_, 2);
v___x_3930_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3931_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3932_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3931_, v_env_3929_, v___x_3930_);
v___x_3933_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3934_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3932_, v___x_3933_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3965_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3965_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3965_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v_fst_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3963_; 
v_fst_3939_ = lean_ctor_get(v_a_3935_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_a_3935_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v_a_3935_, 1);
lean_dec(v_unused_3964_);
v___x_3941_ = v_a_3935_;
v_isShared_3942_ = v_isSharedCheck_3963_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_fst_3939_);
lean_dec(v_a_3935_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3963_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
if (lean_obj_tag(v_fst_3939_) == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
lean_del_object(v___x_3937_);
v___x_3943_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3944_ = l_Lean_MessageData_ofName(v___x_3930_);
lean_inc_ref(v___x_3944_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set_tag(v___x_3941_, 7);
lean_ctor_set(v___x_3941_, 1, v___x_3944_);
lean_ctor_set(v___x_3941_, 0, v___x_3943_);
v___x_3946_ = v___x_3941_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3947_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_3950_ = l_Lean_indentD(v___x_3949_);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3948_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___x_3944_);
v___x_3955_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3956_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_3957_;
}
}
else
{
lean_object* v_val_3959_; lean_object* v___x_3961_; 
lean_del_object(v___x_3941_);
lean_dec(v___x_3930_);
lean_dec(v_stx_2283_);
v_val_3959_ = lean_ctor_get(v_fst_3939_, 0);
lean_inc(v_val_3959_);
lean_dec_ref(v_fst_3939_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v_val_3959_);
v___x_3961_ = v___x_3937_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_val_3959_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v___x_3930_);
lean_dec(v_stx_2283_);
v_a_3966_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3934_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3934_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3974_ = lean_unsigned_to_nat(1u);
v___x_3975_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_3974_);
v___x_3976_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75));
lean_inc(v___x_3975_);
v___x_3977_ = l_Lean_Syntax_isOfKind(v___x_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v_env_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_dec(v___x_3975_);
v___x_3978_ = lean_st_ref_get(v_a_2289_);
v_env_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc_ref(v_env_3979_);
lean_dec(v___x_3978_);
lean_inc_n(v_stx_2283_, 2);
v___x_3980_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_3981_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3982_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3981_, v_env_3979_, v___x_3980_);
v___x_3983_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3984_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_3982_, v___x_3983_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4015_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_4015_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4015_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v_fst_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4013_; 
v_fst_3989_ = lean_ctor_get(v_a_3985_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_a_3985_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; 
v_unused_4014_ = lean_ctor_get(v_a_3985_, 1);
lean_dec(v_unused_4014_);
v___x_3991_ = v_a_3985_;
v_isShared_3992_ = v_isSharedCheck_4013_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_fst_3989_);
lean_dec(v_a_3985_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4013_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
if (lean_obj_tag(v_fst_3989_) == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
lean_del_object(v___x_3987_);
v___x_3993_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3994_ = l_Lean_MessageData_ofName(v___x_3980_);
lean_inc_ref(v___x_3994_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set_tag(v___x_3991_, 7);
lean_ctor_set(v___x_3991_, 1, v___x_3994_);
lean_ctor_set(v___x_3991_, 0, v___x_3993_);
v___x_3996_ = v___x_3991_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_4008_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_3997_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3996_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4000_ = l_Lean_indentD(v___x_3999_);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3998_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
lean_ctor_set(v___x_4004_, 1, v___x_3994_);
v___x_4005_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4004_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
v___x_4007_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4006_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4007_;
}
}
else
{
lean_object* v_val_4009_; lean_object* v___x_4011_; 
lean_del_object(v___x_3991_);
lean_dec(v___x_3980_);
lean_dec(v_stx_2283_);
v_val_4009_ = lean_ctor_get(v_fst_3989_, 0);
lean_inc(v_val_4009_);
lean_dec_ref(v_fst_3989_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v_val_4009_);
v___x_4011_ = v___x_3987_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_val_4009_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v___x_3980_);
lean_dec(v_stx_2283_);
v_a_4016_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3984_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3984_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
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
else
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = l_Lean_Syntax_getArg(v___x_3975_, v___x_3924_);
lean_dec(v___x_3975_);
lean_inc(v___x_4024_);
v___x_4025_ = l_Lean_Syntax_matchesNull(v___x_4024_, v___x_3974_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; lean_object* v_env_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
lean_dec(v___x_4024_);
v___x_4026_ = lean_st_ref_get(v_a_2289_);
v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_env_4027_);
lean_dec(v___x_4026_);
lean_inc_n(v_stx_2283_, 2);
v___x_4028_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_4029_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4030_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4029_, v_env_4027_, v___x_4028_);
v___x_4031_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4032_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_4030_, v___x_4031_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4063_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4063_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4063_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_fst_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4061_; 
v_fst_4037_ = lean_ctor_get(v_a_4033_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_a_4033_);
if (v_isSharedCheck_4061_ == 0)
{
lean_object* v_unused_4062_; 
v_unused_4062_ = lean_ctor_get(v_a_4033_, 1);
lean_dec(v_unused_4062_);
v___x_4039_ = v_a_4033_;
v_isShared_4040_ = v_isSharedCheck_4061_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_fst_4037_);
lean_dec(v_a_4033_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4061_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
if (lean_obj_tag(v_fst_4037_) == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
lean_del_object(v___x_4035_);
v___x_4041_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4042_ = l_Lean_MessageData_ofName(v___x_4028_);
lean_inc_ref(v___x_4042_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set_tag(v___x_4039_, 7);
lean_ctor_set(v___x_4039_, 1, v___x_4042_);
lean_ctor_set(v___x_4039_, 0, v___x_4041_);
v___x_4044_ = v___x_4039_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4041_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4045_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
v___x_4047_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4048_ = l_Lean_indentD(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4046_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
v___x_4050_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
lean_ctor_set(v___x_4052_, 1, v___x_4042_);
v___x_4053_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4052_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4054_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4055_;
}
}
else
{
lean_object* v_val_4057_; lean_object* v___x_4059_; 
lean_del_object(v___x_4039_);
lean_dec(v___x_4028_);
lean_dec(v_stx_2283_);
v_val_4057_ = lean_ctor_get(v_fst_4037_, 0);
lean_inc(v_val_4057_);
lean_dec_ref(v_fst_4037_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v_val_4057_);
v___x_4059_ = v___x_4035_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_val_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v___x_4028_);
lean_dec(v_stx_2283_);
v_a_4064_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4032_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4032_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
v___x_4072_ = l_Lean_Syntax_getArg(v___x_4024_, v___x_3924_);
lean_dec(v___x_4024_);
v___x_4073_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77));
v___x_4074_ = l_Lean_Syntax_isOfKind(v___x_4072_, v___x_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v_env_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4075_ = lean_st_ref_get(v_a_2289_);
v_env_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc_ref(v_env_4076_);
lean_dec(v___x_4075_);
lean_inc_n(v_stx_2283_, 2);
v___x_4077_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_4078_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4079_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4078_, v_env_4076_, v___x_4077_);
v___x_4080_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4081_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_4079_, v___x_4080_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4112_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4112_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4112_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v_fst_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4110_; 
v_fst_4086_ = lean_ctor_get(v_a_4082_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v_a_4082_);
if (v_isSharedCheck_4110_ == 0)
{
lean_object* v_unused_4111_; 
v_unused_4111_ = lean_ctor_get(v_a_4082_, 1);
lean_dec(v_unused_4111_);
v___x_4088_ = v_a_4082_;
v_isShared_4089_ = v_isSharedCheck_4110_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_fst_4086_);
lean_dec(v_a_4082_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4110_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
if (lean_obj_tag(v_fst_4086_) == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
lean_del_object(v___x_4084_);
v___x_4090_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4091_ = l_Lean_MessageData_ofName(v___x_4077_);
lean_inc_ref(v___x_4091_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set_tag(v___x_4088_, 7);
lean_ctor_set(v___x_4088_, 1, v___x_4091_);
lean_ctor_set(v___x_4088_, 0, v___x_4090_);
v___x_4093_ = v___x_4088_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4094_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4097_ = l_Lean_indentD(v___x_4096_);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4095_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
lean_ctor_set(v___x_4101_, 1, v___x_4091_);
v___x_4102_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4103_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4104_;
}
}
else
{
lean_object* v_val_4106_; lean_object* v___x_4108_; 
lean_del_object(v___x_4088_);
lean_dec(v___x_4077_);
lean_dec(v_stx_2283_);
v_val_4106_ = lean_ctor_get(v_fst_4086_, 0);
lean_inc(v_val_4106_);
lean_dec_ref(v_fst_4086_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_val_4106_);
v___x_4108_ = v___x_4084_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_val_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v___x_4077_);
lean_dec(v_stx_2283_);
v_a_4113_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4081_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4081_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
else
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
lean_dec(v_stx_2283_);
v___x_4121_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
}
}
}
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4123_ = lean_unsigned_to_nat(1u);
v___x_4124_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_4123_);
v___x_4125_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4126_ = l_Lean_Syntax_isOfKind(v___x_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v_env_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4127_ = lean_st_ref_get(v_a_2289_);
v_env_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc_ref(v_env_4128_);
lean_dec(v___x_4127_);
lean_inc_n(v_stx_2283_, 2);
v___x_4129_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_4130_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4131_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4130_, v_env_4128_, v___x_4129_);
v___x_4132_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4133_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_4131_, v___x_4132_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4164_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4164_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4164_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v_fst_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4162_; 
v_fst_4138_ = lean_ctor_get(v_a_4134_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_a_4134_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; 
v_unused_4163_ = lean_ctor_get(v_a_4134_, 1);
lean_dec(v_unused_4163_);
v___x_4140_ = v_a_4134_;
v_isShared_4141_ = v_isSharedCheck_4162_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_fst_4138_);
lean_dec(v_a_4134_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4162_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
if (lean_obj_tag(v_fst_4138_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
lean_del_object(v___x_4136_);
v___x_4142_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4143_ = l_Lean_MessageData_ofName(v___x_4129_);
lean_inc_ref(v___x_4143_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set_tag(v___x_4140_, 7);
lean_ctor_set(v___x_4140_, 1, v___x_4143_);
lean_ctor_set(v___x_4140_, 0, v___x_4142_);
v___x_4145_ = v___x_4140_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4142_);
lean_ctor_set(v_reuseFailAlloc_4157_, 1, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4149_ = l_Lean_indentD(v___x_4148_);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4147_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4150_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v___x_4143_);
v___x_4154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4155_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4156_;
}
}
else
{
lean_object* v_val_4158_; lean_object* v___x_4160_; 
lean_del_object(v___x_4140_);
lean_dec(v___x_4129_);
lean_dec(v_stx_2283_);
v_val_4158_ = lean_ctor_get(v_fst_4138_, 0);
lean_inc(v_val_4158_);
lean_dec_ref(v_fst_4138_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 0, v_val_4158_);
v___x_4160_ = v___x_4136_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_val_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v___x_4129_);
lean_dec(v_stx_2283_);
v_a_4165_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4133_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4133_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4173_ = lean_unsigned_to_nat(2u);
v___x_4174_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_4173_);
v___x_4175_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4176_ = l_Lean_Syntax_isOfKind(v___x_4174_, v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v_env_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4177_ = lean_st_ref_get(v_a_2289_);
v_env_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc_ref(v_env_4178_);
lean_dec(v___x_4177_);
lean_inc_n(v_stx_2283_, 2);
v___x_4179_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_4180_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4181_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4180_, v_env_4178_, v___x_4179_);
v___x_4182_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4183_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_4181_, v___x_4182_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4214_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4214_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4214_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v_fst_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4212_; 
v_fst_4188_ = lean_ctor_get(v_a_4184_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_a_4184_);
if (v_isSharedCheck_4212_ == 0)
{
lean_object* v_unused_4213_; 
v_unused_4213_ = lean_ctor_get(v_a_4184_, 1);
lean_dec(v_unused_4213_);
v___x_4190_ = v_a_4184_;
v_isShared_4191_ = v_isSharedCheck_4212_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_fst_4188_);
lean_dec(v_a_4184_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4212_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
if (lean_obj_tag(v_fst_4188_) == 0)
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4195_; 
lean_del_object(v___x_4186_);
v___x_4192_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4193_ = l_Lean_MessageData_ofName(v___x_4179_);
lean_inc_ref(v___x_4193_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set_tag(v___x_4190_, 7);
lean_ctor_set(v___x_4190_, 1, v___x_4193_);
lean_ctor_set(v___x_4190_, 0, v___x_4192_);
v___x_4195_ = v___x_4190_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4192_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4196_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4199_ = l_Lean_indentD(v___x_4198_);
v___x_4200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4197_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
v___x_4201_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4200_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v___x_4193_);
v___x_4204_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4203_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4205_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4206_;
}
}
else
{
lean_object* v_val_4208_; lean_object* v___x_4210_; 
lean_del_object(v___x_4190_);
lean_dec(v___x_4179_);
lean_dec(v_stx_2283_);
v_val_4208_ = lean_ctor_get(v_fst_4188_, 0);
lean_inc(v_val_4208_);
lean_dec_ref(v_fst_4188_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v_val_4208_);
v___x_4210_ = v___x_4186_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_val_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v___x_4179_);
lean_dec(v_stx_2283_);
v_a_4215_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4183_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4183_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_dec(v_stx_2283_);
v___x_4223_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
return v___x_4224_;
}
}
}
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; 
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_4225_);
v___x_4227_ = l_Lean_Syntax_isNone(v___x_4226_);
if (v___x_4227_ == 0)
{
uint8_t v___x_4228_; 
v___x_4228_ = l_Lean_Syntax_matchesNull(v___x_4226_, v___x_4225_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; lean_object* v_env_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_del_object(v___x_2320_);
v___x_4229_ = lean_st_ref_get(v_a_2289_);
v_env_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc_ref(v_env_4230_);
lean_dec(v___x_4229_);
lean_inc_n(v_stx_2283_, 2);
v___x_4231_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_4232_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4233_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4232_, v_env_4230_, v___x_4231_);
v___x_4234_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4235_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_4233_, v___x_4234_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4266_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4266_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4266_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v_fst_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4264_; 
v_fst_4240_ = lean_ctor_get(v_a_4236_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_a_4236_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; 
v_unused_4265_ = lean_ctor_get(v_a_4236_, 1);
lean_dec(v_unused_4265_);
v___x_4242_ = v_a_4236_;
v_isShared_4243_ = v_isSharedCheck_4264_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_fst_4240_);
lean_dec(v_a_4236_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4264_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
if (lean_obj_tag(v_fst_4240_) == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
lean_del_object(v___x_4238_);
v___x_4244_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4245_ = l_Lean_MessageData_ofName(v___x_4231_);
lean_inc_ref(v___x_4245_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set_tag(v___x_4242_, 7);
lean_ctor_set(v___x_4242_, 1, v___x_4245_);
lean_ctor_set(v___x_4242_, 0, v___x_4244_);
v___x_4247_ = v___x_4242_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4248_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4247_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4251_ = l_Lean_indentD(v___x_4250_);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4249_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
lean_ctor_set(v___x_4255_, 1, v___x_4245_);
v___x_4256_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4257_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4258_;
}
}
else
{
lean_object* v_val_4260_; lean_object* v___x_4262_; 
lean_del_object(v___x_4242_);
lean_dec(v___x_4231_);
lean_dec(v_stx_2283_);
v_val_4260_ = lean_ctor_get(v_fst_4240_, 0);
lean_inc(v_val_4260_);
lean_dec_ref(v_fst_4240_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v_val_4260_);
v___x_4262_ = v___x_4238_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_val_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v___x_4231_);
lean_dec(v_stx_2283_);
v_a_4267_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4235_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4235_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
v___y_2408_ = v_a_2284_;
v___y_2409_ = v_a_2285_;
v___y_2410_ = v_a_2286_;
v___y_2411_ = v_a_2287_;
v___y_2412_ = v_a_2288_;
v___y_2413_ = v_a_2289_;
goto v___jp_2407_;
}
}
else
{
lean_dec(v___x_4226_);
v___y_2408_ = v_a_2284_;
v___y_2409_ = v_a_2285_;
v___y_2410_ = v_a_2286_;
v___y_2411_ = v_a_2287_;
v___y_2412_ = v_a_2288_;
v___y_2413_ = v_a_2289_;
goto v___jp_2407_;
}
}
}
else
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
lean_del_object(v___x_2320_);
v___x_4275_ = lean_unsigned_to_nat(1u);
v___x_4276_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_4275_);
lean_dec(v_stx_2283_);
v___x_4277_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4276_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4277_;
}
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
lean_del_object(v___x_2320_);
lean_dec(v_stx_2283_);
v___x_4278_ = lean_unsigned_to_nat(1u);
v___x_4279_ = l_Lean_NameSet_empty;
v___x_4280_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4280_, 0, v___x_4278_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*2, v___x_2524_);
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*2 + 1, v___x_2524_);
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*2 + 2, v___x_2524_);
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
return v___x_4281_;
}
}
else
{
lean_object* v___x_4282_; lean_object* v___x_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
lean_del_object(v___x_2320_);
v___x_4282_ = lean_unsigned_to_nat(0u);
v___x_4287_ = lean_unsigned_to_nat(1u);
v___x_4288_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_4287_);
v___x_4289_ = l_Lean_Syntax_isNone(v___x_4288_);
if (v___x_4289_ == 0)
{
uint8_t v___x_4290_; 
v___x_4290_ = l_Lean_Syntax_matchesNull(v___x_4288_, v___x_4287_);
if (v___x_4290_ == 0)
{
lean_object* v___x_4291_; lean_object* v_env_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4291_ = lean_st_ref_get(v_a_2289_);
v_env_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc_ref(v_env_4292_);
lean_dec(v___x_4291_);
lean_inc_n(v_stx_2283_, 2);
v___x_4293_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_4294_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4295_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4294_, v_env_4292_, v___x_4293_);
v___x_4296_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4297_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_4295_, v___x_4296_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4328_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4328_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4328_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v_fst_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4326_; 
v_fst_4302_ = lean_ctor_get(v_a_4298_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_a_4298_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v_a_4298_, 1);
lean_dec(v_unused_4327_);
v___x_4304_ = v_a_4298_;
v_isShared_4305_ = v_isSharedCheck_4326_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_fst_4302_);
lean_dec(v_a_4298_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4326_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
if (lean_obj_tag(v_fst_4302_) == 0)
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
lean_del_object(v___x_4300_);
v___x_4306_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4307_ = l_Lean_MessageData_ofName(v___x_4293_);
lean_inc_ref(v___x_4307_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 7);
lean_ctor_set(v___x_4304_, 1, v___x_4307_);
lean_ctor_set(v___x_4304_, 0, v___x_4306_);
v___x_4309_ = v___x_4304_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4306_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4310_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_4313_ = l_Lean_indentD(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4311_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
lean_ctor_set(v___x_4317_, 1, v___x_4307_);
v___x_4318_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4319_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_4320_;
}
}
else
{
lean_object* v_val_4322_; lean_object* v___x_4324_; 
lean_del_object(v___x_4304_);
lean_dec(v___x_4293_);
lean_dec(v_stx_2283_);
v_val_4322_ = lean_ctor_get(v_fst_4302_, 0);
lean_inc(v_val_4322_);
lean_dec_ref(v_fst_4302_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v_val_4322_);
v___x_4324_ = v___x_4300_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_val_4322_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec(v___x_4293_);
lean_dec(v_stx_2283_);
v_a_4329_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4297_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4297_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
else
{
lean_dec(v_stx_2283_);
goto v___jp_4283_;
}
}
else
{
lean_dec(v___x_4288_);
lean_dec(v_stx_2283_);
goto v___jp_4283_;
}
v___jp_4283_:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4284_ = l_Lean_NameSet_empty;
v___x_4285_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4285_, 0, v___x_4282_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
lean_ctor_set_uint8(v___x_4285_, sizeof(void*)*2, v___x_2522_);
lean_ctor_set_uint8(v___x_4285_, sizeof(void*)*2 + 1, v___x_2522_);
lean_ctor_set_uint8(v___x_4285_, sizeof(void*)*2 + 2, v___x_2520_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
return v___x_4286_;
}
}
}
else
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_del_object(v___x_2320_);
lean_dec(v_stx_2283_);
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = l_Lean_NameSet_empty;
v___x_4339_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4339_, 0, v___x_4337_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
lean_ctor_set_uint8(v___x_4339_, sizeof(void*)*2, v___x_2519_);
lean_ctor_set_uint8(v___x_4339_, sizeof(void*)*2 + 1, v___x_2520_);
lean_ctor_set_uint8(v___x_4339_, sizeof(void*)*2 + 2, v___x_2519_);
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
return v___x_4340_;
}
}
else
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
lean_del_object(v___x_2320_);
lean_dec(v_stx_2283_);
v___x_4341_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78);
v___x_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
return v___x_4342_;
}
v___jp_2336_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2343_ = lean_unsigned_to_nat(2u);
v___x_2344_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2343_);
v___x_2345_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2346_ = l_Lean_Syntax_isOfKind(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v_env_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2347_ = lean_st_ref_get(v___y_2342_);
v_env_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc_ref(v_env_2348_);
lean_dec(v___x_2347_);
lean_inc_n(v_stx_2283_, 2);
v___x_2349_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2350_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2351_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2350_, v_env_2348_, v___x_2349_);
v___x_2352_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2353_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2351_, v___x_2352_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2384_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2384_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2384_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_fst_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2382_; 
v_fst_2358_ = lean_ctor_get(v_a_2354_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_a_2354_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v_a_2354_, 1);
lean_dec(v_unused_2383_);
v___x_2360_ = v_a_2354_;
v_isShared_2361_ = v_isSharedCheck_2382_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_fst_2358_);
lean_dec(v_a_2354_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2382_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
if (lean_obj_tag(v_fst_2358_) == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
lean_del_object(v___x_2356_);
v___x_2362_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2363_ = l_Lean_MessageData_ofName(v___x_2349_);
lean_inc_ref(v___x_2363_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 7);
lean_ctor_set(v___x_2360_, 1, v___x_2363_);
lean_ctor_set(v___x_2360_, 0, v___x_2362_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2366_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2369_ = l_Lean_indentD(v___x_2368_);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2367_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v___x_2363_);
v___x_2374_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2375_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2376_;
}
}
else
{
lean_object* v_val_2378_; lean_object* v___x_2380_; 
lean_del_object(v___x_2360_);
lean_dec(v___x_2349_);
lean_dec(v_stx_2283_);
v_val_2378_ = lean_ctor_get(v_fst_2358_, 0);
lean_inc(v_val_2378_);
lean_dec_ref(v_fst_2358_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v_val_2378_);
v___x_2380_ = v___x_2356_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_val_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v___x_2349_);
lean_dec(v_stx_2283_);
v_a_2385_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2353_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2353_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2393_ = lean_unsigned_to_nat(7u);
v___x_2394_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2393_);
v___x_2395_ = lean_unsigned_to_nat(8u);
v___x_2396_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2395_);
lean_dec(v_stx_2283_);
v___x_2397_ = l_Lean_Syntax_getOptional_x3f(v___x_2396_);
lean_dec(v___x_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_box(0);
v___y_2292_ = v___y_2341_;
v___y_2293_ = v___y_2340_;
v___y_2294_ = v___y_2337_;
v___y_2295_ = v___y_2338_;
v___y_2296_ = v___y_2342_;
v___y_2297_ = v___y_2339_;
v___y_2298_ = v___x_2394_;
v___y_2299_ = v___x_2398_;
goto v___jp_2291_;
}
else
{
lean_object* v_val_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
v_val_2399_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2397_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_val_2399_);
lean_dec(v___x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_val_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
v___y_2292_ = v___y_2341_;
v___y_2293_ = v___y_2340_;
v___y_2294_ = v___y_2337_;
v___y_2295_ = v___y_2338_;
v___y_2296_ = v___y_2342_;
v___y_2297_ = v___y_2339_;
v___y_2298_ = v___x_2394_;
v___y_2299_ = v___x_2404_;
goto v___jp_2291_;
}
}
}
}
}
v___jp_2407_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2414_ = lean_unsigned_to_nat(2u);
v___x_2415_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2414_);
v___x_2416_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2417_ = l_Lean_Syntax_isOfKind(v___x_2415_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v_env_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_del_object(v___x_2320_);
v___x_2418_ = lean_st_ref_get(v___y_2413_);
v_env_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc_ref(v_env_2419_);
lean_dec(v___x_2418_);
lean_inc_n(v_stx_2283_, 2);
v___x_2420_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2421_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2422_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2421_, v_env_2419_, v___x_2420_);
v___x_2423_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2424_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2422_, v___x_2423_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2455_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2455_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2455_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_fst_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2453_; 
v_fst_2429_ = lean_ctor_get(v_a_2425_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v_a_2425_, 1);
lean_dec(v_unused_2454_);
v___x_2431_ = v_a_2425_;
v_isShared_2432_ = v_isSharedCheck_2453_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_fst_2429_);
lean_dec(v_a_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2453_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
if (lean_obj_tag(v_fst_2429_) == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
lean_del_object(v___x_2427_);
v___x_2433_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2434_ = l_Lean_MessageData_ofName(v___x_2420_);
lean_inc_ref(v___x_2434_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 7);
lean_ctor_set(v___x_2431_, 1, v___x_2434_);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2437_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2440_ = l_Lean_indentD(v___x_2439_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2438_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v___x_2434_);
v___x_2445_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2446_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v___x_2447_;
}
}
else
{
lean_object* v_val_2449_; lean_object* v___x_2451_; 
lean_del_object(v___x_2431_);
lean_dec(v___x_2420_);
lean_dec(v_stx_2283_);
v_val_2449_ = lean_ctor_get(v_fst_2429_, 0);
lean_inc(v_val_2449_);
lean_dec_ref(v_fst_2429_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_val_2449_);
v___x_2451_ = v___x_2427_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_val_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v___x_2420_);
lean_dec(v_stx_2283_);
v_a_2456_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2424_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2424_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2464_ = lean_unsigned_to_nat(3u);
v___x_2465_ = l_Lean_Syntax_getArg(v_stx_2283_, v___x_2464_);
v___x_2466_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2467_ = l_Lean_Syntax_isOfKind(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v_env_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_del_object(v___x_2320_);
v___x_2468_ = lean_st_ref_get(v___y_2413_);
v_env_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_env_2469_);
lean_dec(v___x_2468_);
lean_inc_n(v_stx_2283_, 2);
v___x_2470_ = l_Lean_Syntax_getKind(v_stx_2283_);
v___x_2471_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2472_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2471_, v_env_2469_, v___x_2470_);
v___x_2473_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2474_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2283_, v___x_2472_, v___x_2473_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2505_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2505_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2505_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_fst_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2503_; 
v_fst_2479_ = lean_ctor_get(v_a_2475_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2475_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v_a_2475_, 1);
lean_dec(v_unused_2504_);
v___x_2481_ = v_a_2475_;
v_isShared_2482_ = v_isSharedCheck_2503_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_fst_2479_);
lean_dec(v_a_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2503_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
if (lean_obj_tag(v_fst_2479_) == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
lean_del_object(v___x_2477_);
v___x_2483_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2484_ = l_Lean_MessageData_ofName(v___x_2470_);
lean_inc_ref(v___x_2484_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set_tag(v___x_2481_, 7);
lean_ctor_set(v___x_2481_, 1, v___x_2484_);
lean_ctor_set(v___x_2481_, 0, v___x_2483_);
v___x_2486_ = v___x_2481_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2487_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_MessageData_ofSyntax(v_stx_2283_);
v___x_2490_ = l_Lean_indentD(v___x_2489_);
v___x_2491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2488_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2484_);
v___x_2495_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2496_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v___x_2497_;
}
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2501_; 
lean_del_object(v___x_2481_);
lean_dec(v___x_2470_);
lean_dec(v_stx_2283_);
v_val_2499_ = lean_ctor_get(v_fst_2479_, 0);
lean_inc(v_val_2499_);
lean_dec_ref(v_fst_2479_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v_val_2499_);
v___x_2501_ = v___x_2477_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_val_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v___x_2470_);
lean_dec(v_stx_2283_);
v_a_2506_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2474_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2474_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_dec(v_stx_2283_);
v___x_2514_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2514_);
v___x_2516_ = v___x_2320_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_stx_2283_);
v_a_4344_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_2317_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_2317_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
v___jp_2291_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2301_ = lean_box(0);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___y_2298_);
v___x_2303_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2300_, v___x_2301_, v___x_2302_, v___y_2299_, v___y_2294_, v___y_2295_, v___y_2297_, v___y_2293_, v___y_2292_, v___y_2296_);
return v___x_2303_;
}
v___jp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2305_, v_bodyInfo_2306_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
v___jp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2310_, v_bodyInfo_2311_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4352_, size_t v_sz_4353_, size_t v_i_4354_, lean_object* v_b_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v___x_4363_; 
v___x_4363_ = lean_usize_dec_lt(v_i_4354_, v_sz_4353_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v_b_4355_);
return v___x_4364_;
}
else
{
uint8_t v_breaks_4365_; uint8_t v_continues_4366_; uint8_t v_returnsEarly_4367_; lean_object* v_numRegularExits_4368_; lean_object* v_reassigns_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v_breaks_4365_ = lean_ctor_get_uint8(v_b_4355_, sizeof(void*)*2);
v_continues_4366_ = lean_ctor_get_uint8(v_b_4355_, sizeof(void*)*2 + 1);
v_returnsEarly_4367_ = lean_ctor_get_uint8(v_b_4355_, sizeof(void*)*2 + 2);
v_numRegularExits_4368_ = lean_ctor_get(v_b_4355_, 0);
v_reassigns_4369_ = lean_ctor_get(v_b_4355_, 1);
v___x_4370_ = lean_unsigned_to_nat(0u);
v___x_4371_ = lean_nat_dec_eq(v_numRegularExits_4368_, v___x_4370_);
if (v___x_4371_ == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4373_; 
lean_inc(v_reassigns_4369_);
lean_dec_ref(v_b_4355_);
v_a_4372_ = lean_array_uget_borrowed(v_as_4352_, v_i_4354_);
lean_inc(v_a_4372_);
v___x_4373_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4372_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; uint8_t v___y_4376_; uint8_t v___y_4377_; uint8_t v___y_4378_; uint8_t v___y_4393_; uint8_t v___y_4394_; uint8_t v___y_4397_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
lean_dec_ref(v___x_4373_);
if (v_breaks_4365_ == 0)
{
uint8_t v_breaks_4399_; 
v_breaks_4399_ = lean_ctor_get_uint8(v_a_4374_, sizeof(void*)*2);
v___y_4397_ = v_breaks_4399_;
goto v___jp_4396_;
}
else
{
v___y_4397_ = v___x_4363_;
goto v___jp_4396_;
}
v___jp_4375_:
{
lean_object* v_numRegularExits_4379_; lean_object* v_reassigns_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4391_; 
v_numRegularExits_4379_ = lean_ctor_get(v_a_4374_, 0);
v_reassigns_4380_ = lean_ctor_get(v_a_4374_, 1);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_a_4374_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4382_ = v_a_4374_;
v_isShared_4383_ = v_isSharedCheck_4391_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_reassigns_4380_);
lean_inc(v_numRegularExits_4379_);
lean_dec(v_a_4374_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4391_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = l_Lean_NameSet_append(v_reassigns_4369_, v_reassigns_4380_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 1, v___x_4384_);
v___x_4386_ = v___x_4382_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_numRegularExits_4379_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v___x_4384_);
v___x_4386_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
size_t v___x_4387_; size_t v___x_4388_; 
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*2, v___y_4377_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*2 + 1, v___y_4376_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*2 + 2, v___y_4378_);
v___x_4387_ = ((size_t)1ULL);
v___x_4388_ = lean_usize_add(v_i_4354_, v___x_4387_);
v_i_4354_ = v___x_4388_;
v_b_4355_ = v___x_4386_;
goto _start;
}
}
}
v___jp_4392_:
{
if (v_returnsEarly_4367_ == 0)
{
uint8_t v_returnsEarly_4395_; 
v_returnsEarly_4395_ = lean_ctor_get_uint8(v_a_4374_, sizeof(void*)*2 + 2);
v___y_4376_ = v___y_4394_;
v___y_4377_ = v___y_4393_;
v___y_4378_ = v_returnsEarly_4395_;
goto v___jp_4375_;
}
else
{
v___y_4376_ = v___y_4394_;
v___y_4377_ = v___y_4393_;
v___y_4378_ = v___x_4363_;
goto v___jp_4375_;
}
}
v___jp_4396_:
{
if (v_continues_4366_ == 0)
{
uint8_t v_continues_4398_; 
v_continues_4398_ = lean_ctor_get_uint8(v_a_4374_, sizeof(void*)*2 + 1);
v___y_4393_ = v___y_4397_;
v___y_4394_ = v_continues_4398_;
goto v___jp_4392_;
}
else
{
v___y_4393_ = v___y_4397_;
v___y_4394_ = v___x_4363_;
goto v___jp_4392_;
}
}
}
else
{
lean_dec(v_reassigns_4369_);
return v___x_4373_;
}
}
else
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_b_4355_);
return v___x_4400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_info_4409_; lean_object* v___x_4410_; size_t v_sz_4411_; size_t v___x_4412_; lean_object* v___x_4413_; 
v_info_4409_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4410_ = l_Lean_Parser_Term_getDoElems(v_stx_4401_);
v_sz_4411_ = lean_array_size(v___x_4410_);
v___x_4412_ = ((size_t)0ULL);
v___x_4413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4410_, v_sz_4411_, v___x_4412_, v_info_4409_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
lean_dec_ref(v___x_4410_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
lean_dec(v_a_4418_);
lean_dec_ref(v_a_4417_);
lean_dec(v_a_4416_);
lean_dec_ref(v_a_4415_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
lean_dec(v_a_4429_);
lean_dec_ref(v_a_4428_);
lean_dec(v_a_4427_);
lean_dec_ref(v_a_4426_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4432_, lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_b_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
size_t v_sz_boxed_4443_; size_t v_i_boxed_4444_; lean_object* v_res_4445_; 
v_sz_boxed_4443_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4444_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4432_, v_sz_boxed_4443_, v_i_boxed_4444_, v_b_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_as_4432_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4446_, lean_object* v_sz_4447_, lean_object* v_i_4448_, lean_object* v_b_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
size_t v_sz_boxed_4457_; size_t v_i_boxed_4458_; lean_object* v_res_4459_; 
v_sz_boxed_4457_ = lean_unbox_usize(v_sz_4447_);
lean_dec(v_sz_4447_);
v_i_boxed_4458_ = lean_unbox_usize(v_i_4448_);
lean_dec(v_i_4448_);
v_res_4459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4446_, v_sz_boxed_4457_, v_i_boxed_4458_, v_b_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec_ref(v_as_4446_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4460_, lean_object* v_rhs_x3f_4461_, lean_object* v_otherwise_x3f_4462_, lean_object* v_body_x3f_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4460_, v_rhs_x3f_4461_, v_otherwise_x3f_4462_, v_body_x3f_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4472_, lean_object* v_as_4473_, lean_object* v_sz_4474_, lean_object* v_i_4475_, lean_object* v_b_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v___x_282299__boxed_4484_; size_t v_sz_boxed_4485_; size_t v_i_boxed_4486_; lean_object* v_res_4487_; 
v___x_282299__boxed_4484_ = lean_unbox(v___x_4472_);
v_sz_boxed_4485_ = lean_unbox_usize(v_sz_4474_);
lean_dec(v_sz_4474_);
v_i_boxed_4486_ = lean_unbox_usize(v_i_4475_);
lean_dec(v_i_4475_);
v_res_4487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_282299__boxed_4484_, v_as_4473_, v_sz_boxed_4485_, v_i_boxed_4486_, v_b_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec_ref(v_as_4473_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4488_, lean_object* v_as_4489_, lean_object* v_sz_4490_, lean_object* v_i_4491_, lean_object* v_b_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
uint8_t v___x_282350__boxed_4500_; size_t v_sz_boxed_4501_; size_t v_i_boxed_4502_; lean_object* v_res_4503_; 
v___x_282350__boxed_4500_ = lean_unbox(v___x_4488_);
v_sz_boxed_4501_ = lean_unbox_usize(v_sz_4490_);
lean_dec(v_sz_4490_);
v_i_boxed_4502_ = lean_unbox_usize(v_i_4491_);
lean_dec(v_i_4491_);
v_res_4503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_282350__boxed_4500_, v_as_4489_, v_sz_boxed_4501_, v_i_boxed_4502_, v_b_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec_ref(v_as_4489_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4504_, lean_object* v_sz_4505_, lean_object* v_i_4506_, lean_object* v_b_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
size_t v_sz_boxed_4515_; size_t v_i_boxed_4516_; lean_object* v_res_4517_; 
v_sz_boxed_4515_ = lean_unbox_usize(v_sz_4505_);
lean_dec(v_sz_4505_);
v_i_boxed_4516_ = lean_unbox_usize(v_i_4506_);
lean_dec(v_i_4506_);
v_res_4517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4504_, v_sz_boxed_4515_, v_i_boxed_4516_, v_b_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec_ref(v_as_4504_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4518_, lean_object* v_decl_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
uint8_t v_reassignment_boxed_4527_; lean_object* v_res_4528_; 
v_reassignment_boxed_4527_ = lean_unbox(v_reassignment_4518_);
v_res_4528_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4527_, v_decl_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4556_, lean_object* v_ref_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4557_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4566_, lean_object* v_ref_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4566_, v_ref_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4586_, lean_object* v_x_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4586_, v_x_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4596_, lean_object* v_as_4597_, lean_object* v_as_x27_4598_, lean_object* v_b_4599_, lean_object* v_a_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4596_, v_as_x27_4598_, v_b_4599_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4609_, lean_object* v_as_4610_, lean_object* v_as_x27_4611_, lean_object* v_b_4612_, lean_object* v_a_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4609_, v_as_4610_, v_as_x27_4611_, v_b_4612_, v_a_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v_as_4610_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4622_, lean_object* v_msg_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4632_, lean_object* v_msg_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4632_, v_msg_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4642_, lean_object* v_msg_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4642_, v_msg_4643_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4652_, lean_object* v_msg_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4652_, v_msg_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4662_, lean_object* v_as_x27_4663_, lean_object* v_b_4664_, lean_object* v_a_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4663_, v_b_4664_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4674_, lean_object* v_as_x27_4675_, lean_object* v_b_4676_, lean_object* v_a_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4674_, v_as_x27_4675_, v_b_4676_, v_a_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v_as_4674_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4686_, lean_object* v_ref_4687_, lean_object* v_msg_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v___x_4696_; 
v___x_4696_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4687_, v_msg_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4697_, lean_object* v_ref_4698_, lean_object* v_msg_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4697_, v_ref_4698_, v_msg_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v_ref_4698_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4708_, lean_object* v_macroStack_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4708_, v_macroStack_4709_, v___y_4714_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4718_, lean_object* v_macroStack_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4718_, v_macroStack_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4728_, lean_object* v_m_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4729_, v_a_4730_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4732_, lean_object* v_m_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4732_, v_m_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_m_4733_);
return v_res_4735_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4736_, lean_object* v_x_4737_, lean_object* v_x_4738_){
_start:
{
uint8_t v___x_4739_; 
v___x_4739_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4737_, v_x_4738_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4740_, lean_object* v_x_4741_, lean_object* v_x_4742_){
_start:
{
uint8_t v_res_4743_; lean_object* v_r_4744_; 
v_res_4743_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4740_, v_x_4741_, v_x_4742_);
lean_dec_ref(v_x_4742_);
lean_dec_ref(v_x_4741_);
v_r_4744_ = lean_box(v_res_4743_);
return v_r_4744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4745_, lean_object* v_a_4746_, lean_object* v_x_4747_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4746_, v_x_4747_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4749_, lean_object* v_a_4750_, lean_object* v_x_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4749_, v_a_4750_, v_x_4751_);
lean_dec(v_x_4751_);
lean_dec(v_a_4750_);
return v_res_4752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4753_, lean_object* v_x_4754_, size_t v_x_4755_, lean_object* v_x_4756_){
_start:
{
uint8_t v___x_4757_; 
v___x_4757_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4754_, v_x_4755_, v_x_4756_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4758_, lean_object* v_x_4759_, lean_object* v_x_4760_, lean_object* v_x_4761_){
_start:
{
size_t v_x_288007__boxed_4762_; uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_x_288007__boxed_4762_ = lean_unbox_usize(v_x_4760_);
lean_dec(v_x_4760_);
v_res_4763_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4758_, v_x_4759_, v_x_288007__boxed_4762_, v_x_4761_);
lean_dec_ref(v_x_4761_);
lean_dec_ref(v_x_4759_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4765_, lean_object* v_keys_4766_, lean_object* v_vals_4767_, lean_object* v_heq_4768_, lean_object* v_i_4769_, lean_object* v_k_4770_){
_start:
{
uint8_t v___x_4771_; 
v___x_4771_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4766_, v_i_4769_, v_k_4770_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4772_, lean_object* v_keys_4773_, lean_object* v_vals_4774_, lean_object* v_heq_4775_, lean_object* v_i_4776_, lean_object* v_k_4777_){
_start:
{
uint8_t v_res_4778_; lean_object* v_r_4779_; 
v_res_4778_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4772_, v_keys_4773_, v_vals_4774_, v_heq_4775_, v_i_4776_, v_k_4777_);
lean_dec_ref(v_k_4777_);
lean_dec_ref(v_vals_4774_);
lean_dec_ref(v_keys_4773_);
v_r_4779_ = lean_box(v_res_4778_);
return v_r_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4788_; 
v___x_4788_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
return v___x_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_);
lean_dec(v_a_4795_);
lean_dec_ref(v_a_4794_);
lean_dec(v_a_4793_);
lean_dec_ref(v_a_4792_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_);
lean_dec(v_a_4813_);
lean_dec_ref(v_a_4812_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
return v_res_4815_;
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
