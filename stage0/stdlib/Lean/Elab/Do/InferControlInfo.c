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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(72) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(80) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(79) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(79) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83;
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
uint8_t v_breaks_10_; uint8_t v_continues_11_; uint8_t v_returnsEarly_12_; lean_object* v_numRegularExits_13_; lean_object* v_reassigns_14_; uint8_t v___y_16_; uint8_t v___y_17_; uint8_t v___y_18_; lean_object* v___y_19_; uint8_t v___y_31_; uint8_t v___y_32_; uint8_t v___y_33_; uint8_t v___y_38_; uint8_t v___y_39_; uint8_t v___y_42_; 
v_breaks_10_ = lean_ctor_get_uint8(v_a_8_, sizeof(void*)*2);
v_continues_11_ = lean_ctor_get_uint8(v_a_8_, sizeof(void*)*2 + 1);
v_returnsEarly_12_ = lean_ctor_get_uint8(v_a_8_, sizeof(void*)*2 + 2);
v_numRegularExits_13_ = lean_ctor_get(v_a_8_, 0);
lean_inc(v_numRegularExits_13_);
v_reassigns_14_ = lean_ctor_get(v_a_8_, 1);
lean_inc(v_reassigns_14_);
lean_dec_ref(v_a_8_);
if (v_breaks_10_ == 0)
{
uint8_t v_breaks_44_; 
v_breaks_44_ = lean_ctor_get_uint8(v_b_9_, sizeof(void*)*2);
v___y_42_ = v_breaks_44_;
goto v___jp_41_;
}
else
{
v___y_42_ = v_breaks_10_;
goto v___jp_41_;
}
v___jp_15_:
{
lean_object* v_reassigns_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_reassigns_20_ = lean_ctor_get(v_b_9_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_b_9_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v_b_9_, 0);
lean_dec(v_unused_29_);
v___x_22_ = v_b_9_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_reassigns_20_);
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
lean_ctor_set(v___x_22_, 0, v___y_19_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___y_19_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*2, v___y_16_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*2 + 1, v___y_18_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*2 + 2, v___y_17_);
return v___x_26_;
}
}
}
v___jp_30_:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_nat_dec_eq(v_numRegularExits_13_, v___x_34_);
lean_dec(v_numRegularExits_13_);
if (v___x_35_ == 0)
{
lean_object* v_numRegularExits_36_; 
v_numRegularExits_36_ = lean_ctor_get(v_b_9_, 0);
lean_inc(v_numRegularExits_36_);
v___y_16_ = v___y_31_;
v___y_17_ = v___y_33_;
v___y_18_ = v___y_32_;
v___y_19_ = v_numRegularExits_36_;
goto v___jp_15_;
}
else
{
v___y_16_ = v___y_31_;
v___y_17_ = v___y_33_;
v___y_18_ = v___y_32_;
v___y_19_ = v___x_34_;
goto v___jp_15_;
}
}
v___jp_37_:
{
if (v_returnsEarly_12_ == 0)
{
uint8_t v_returnsEarly_40_; 
v_returnsEarly_40_ = lean_ctor_get_uint8(v_b_9_, sizeof(void*)*2 + 2);
v___y_31_ = v___y_38_;
v___y_32_ = v___y_39_;
v___y_33_ = v_returnsEarly_40_;
goto v___jp_30_;
}
else
{
v___y_31_ = v___y_38_;
v___y_32_ = v___y_39_;
v___y_33_ = v_returnsEarly_12_;
goto v___jp_30_;
}
}
v___jp_41_:
{
if (v_continues_11_ == 0)
{
uint8_t v_continues_43_; 
v_continues_43_ = lean_ctor_get_uint8(v_b_9_, sizeof(void*)*2 + 1);
v___y_38_ = v___y_42_;
v___y_39_ = v_continues_43_;
goto v___jp_37_;
}
else
{
v___y_38_ = v___y_42_;
v___y_39_ = v_continues_11_;
goto v___jp_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_45_, lean_object* v_b_46_){
_start:
{
uint8_t v_breaks_47_; uint8_t v_continues_48_; uint8_t v_returnsEarly_49_; lean_object* v_numRegularExits_50_; lean_object* v_reassigns_51_; uint8_t v___y_53_; uint8_t v___y_54_; uint8_t v___y_55_; uint8_t v___y_68_; uint8_t v___y_69_; uint8_t v___y_72_; 
v_breaks_47_ = lean_ctor_get_uint8(v_a_45_, sizeof(void*)*2);
v_continues_48_ = lean_ctor_get_uint8(v_a_45_, sizeof(void*)*2 + 1);
v_returnsEarly_49_ = lean_ctor_get_uint8(v_a_45_, sizeof(void*)*2 + 2);
v_numRegularExits_50_ = lean_ctor_get(v_a_45_, 0);
lean_inc(v_numRegularExits_50_);
v_reassigns_51_ = lean_ctor_get(v_a_45_, 1);
lean_inc(v_reassigns_51_);
lean_dec_ref(v_a_45_);
if (v_breaks_47_ == 0)
{
uint8_t v_breaks_74_; 
v_breaks_74_ = lean_ctor_get_uint8(v_b_46_, sizeof(void*)*2);
v___y_72_ = v_breaks_74_;
goto v___jp_71_;
}
else
{
v___y_72_ = v_breaks_47_;
goto v___jp_71_;
}
v___jp_52_:
{
lean_object* v_numRegularExits_56_; lean_object* v_reassigns_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_66_; 
v_numRegularExits_56_ = lean_ctor_get(v_b_46_, 0);
v_reassigns_57_ = lean_ctor_get(v_b_46_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_b_46_);
if (v_isSharedCheck_66_ == 0)
{
v___x_59_ = v_b_46_;
v_isShared_60_ = v_isSharedCheck_66_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_reassigns_57_);
lean_inc(v_numRegularExits_56_);
lean_dec(v_b_46_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_66_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_61_ = lean_nat_add(v_numRegularExits_50_, v_numRegularExits_56_);
lean_dec(v_numRegularExits_56_);
lean_dec(v_numRegularExits_50_);
v___x_62_ = l_Lean_NameSet_append(v_reassigns_51_, v_reassigns_57_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_62_);
lean_ctor_set(v___x_59_, 0, v___x_61_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_ctor_set_uint8(v___x_64_, sizeof(void*)*2, v___y_53_);
lean_ctor_set_uint8(v___x_64_, sizeof(void*)*2 + 1, v___y_54_);
lean_ctor_set_uint8(v___x_64_, sizeof(void*)*2 + 2, v___y_55_);
return v___x_64_;
}
}
}
v___jp_67_:
{
if (v_returnsEarly_49_ == 0)
{
uint8_t v_returnsEarly_70_; 
v_returnsEarly_70_ = lean_ctor_get_uint8(v_b_46_, sizeof(void*)*2 + 2);
v___y_53_ = v___y_68_;
v___y_54_ = v___y_69_;
v___y_55_ = v_returnsEarly_70_;
goto v___jp_52_;
}
else
{
v___y_53_ = v___y_68_;
v___y_54_ = v___y_69_;
v___y_55_ = v_returnsEarly_49_;
goto v___jp_52_;
}
}
v___jp_71_:
{
if (v_continues_48_ == 0)
{
uint8_t v_continues_73_; 
v_continues_73_ = lean_ctor_get_uint8(v_b_46_, sizeof(void*)*2 + 1);
v___y_68_ = v___y_72_;
v___y_69_ = v_continues_73_;
goto v___jp_67_;
}
else
{
v___y_68_ = v___y_72_;
v___y_69_ = v_continues_48_;
goto v___jp_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_75_, lean_object* v_x2_76_, lean_object* v_x3_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v_x1_75_);
lean_ctor_set(v___x_78_, 1, v_x3_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_81_ = l_Lean_stringToMessageData(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2));
v___x_84_ = l_Lean_stringToMessageData(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_107_ = l_Lean_stringToMessageData(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_112_ = l_Lean_stringToMessageData(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_115_ = l_Lean_stringToMessageData(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_116_, lean_object* v_info_117_){
_start:
{
uint8_t v_breaks_118_; uint8_t v_continues_119_; uint8_t v_returnsEarly_120_; lean_object* v_numRegularExits_121_; lean_object* v_reassigns_122_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___x_154_; lean_object* v___y_156_; 
v_breaks_118_ = lean_ctor_get_uint8(v_info_117_, sizeof(void*)*2);
v_continues_119_ = lean_ctor_get_uint8(v_info_117_, sizeof(void*)*2 + 1);
v_returnsEarly_120_ = lean_ctor_get_uint8(v_info_117_, sizeof(void*)*2 + 2);
v_numRegularExits_121_ = lean_ctor_get(v_info_117_, 0);
lean_inc(v_numRegularExits_121_);
v_reassigns_122_ = lean_ctor_get(v_info_117_, 1);
lean_inc(v_reassigns_122_);
lean_dec_ref(v_info_117_);
v___x_154_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
if (v_breaks_118_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_156_ = v___x_164_;
goto v___jp_155_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_156_ = v___x_165_;
goto v___jp_155_;
}
v___jp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_inc_ref(v___y_125_);
v___x_126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_126_, 0, v___y_125_);
v___x_127_ = l_Lean_MessageData_ofFormat(v___x_126_);
v___x_128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_128_, 0, v___y_124_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = l_Nat_reprFast(v_numRegularExits_121_);
v___x_132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___x_133_ = l_Lean_MessageData_ofFormat(v___x_132_);
v___x_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_130_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3);
v___x_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_box(0);
v___x_138_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_139_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_138_, v___f_116_, v___x_137_, v_reassigns_122_);
v___x_140_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14));
v___x_141_ = l_List_mapTR_loop___redArg(v___x_140_, v___x_139_, v___x_137_);
v___x_142_ = l_Lean_MessageData_ofList(v___x_141_);
v___x_143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_136_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
return v___x_143_;
}
v___jp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_inc_ref(v___y_146_);
v___x_147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_147_, 0, v___y_146_);
v___x_148_ = l_Lean_MessageData_ofFormat(v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___y_145_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
if (v_returnsEarly_120_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_124_ = v___x_151_;
v___y_125_ = v___x_152_;
goto v___jp_123_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_124_ = v___x_151_;
v___y_125_ = v___x_153_;
goto v___jp_123_;
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc_ref(v___y_156_);
v___x_157_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_157_, 0, v___y_156_);
v___x_158_ = l_Lean_MessageData_ofFormat(v___x_157_);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_154_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
if (v_continues_119_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_145_ = v___x_161_;
v___y_146_ = v___x_162_;
goto v___jp_144_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_145_ = v___x_161_;
v___y_146_ = v___x_163_;
goto v___jp_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_196_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_197_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_198_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_199_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_200_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_201_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_196_, v___x_197_, v___x_198_, v___x_199_, v___x_200_, v_ref_194_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_213_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_219_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_220_ = l_Lean_addBuiltinDocString(v___x_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_251_ = l_Lean_addBuiltinDeclarationRanges(v___x_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; lean_object* v_env_261_; lean_object* v___x_262_; lean_object* v_mctx_263_; lean_object* v_lctx_264_; lean_object* v_options_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_260_ = lean_st_ref_get(v___y_258_);
v_env_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_env_261_);
lean_dec(v___x_260_);
v___x_262_ = lean_st_ref_get(v___y_256_);
v_mctx_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc_ref(v_mctx_263_);
lean_dec(v___x_262_);
v_lctx_264_ = lean_ctor_get(v___y_255_, 2);
v_options_265_ = lean_ctor_get(v___y_257_, 2);
lean_inc_ref(v_options_265_);
lean_inc_ref(v_lctx_264_);
v___x_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_266_, 0, v_env_261_);
lean_ctor_set(v___x_266_, 1, v_mctx_263_);
lean_ctor_set(v___x_266_, 2, v_lctx_264_);
lean_ctor_set(v___x_266_, 3, v_options_265_);
v___x_267_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_msgData_254_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(1);
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
return v_x_283_;
}
else
{
lean_object* v_head_285_; lean_object* v_tail_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_308_; 
v_head_285_ = lean_ctor_get(v_x_284_, 0);
v_tail_286_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_308_ == 0)
{
v___x_288_ = v_x_284_;
v_isShared_289_ = v_isSharedCheck_308_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_tail_286_);
lean_inc(v_head_285_);
lean_dec(v_x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_308_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_before_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_306_; 
v_before_290_ = lean_ctor_get(v_head_285_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_head_285_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_head_285_, 1);
lean_dec(v_unused_307_);
v___x_292_ = v_head_285_;
v_isShared_293_ = v_isSharedCheck_306_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_before_290_);
lean_dec(v_head_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_306_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 7);
lean_ctor_set(v___x_292_, 1, v___x_294_);
lean_ctor_set(v___x_292_, 0, v_x_283_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_x_283_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_305_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 7);
lean_ctor_set(v___x_288_, 1, v___x_297_);
lean_ctor_set(v___x_288_, 0, v___x_296_);
v___x_299_ = v___x_288_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_304_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_MessageData_ofSyntax(v_before_290_);
v___x_301_ = l_Lean_indentD(v___x_300_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v_x_283_ = v___x_302_;
v_x_284_ = v_tail_286_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_309_, lean_object* v_opt_310_){
_start:
{
lean_object* v_name_311_; lean_object* v_defValue_312_; lean_object* v_map_313_; lean_object* v___x_314_; 
v_name_311_ = lean_ctor_get(v_opt_310_, 0);
v_defValue_312_ = lean_ctor_get(v_opt_310_, 1);
v_map_313_ = lean_ctor_get(v_opts_309_, 0);
v___x_314_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_313_, v_name_311_);
if (lean_obj_tag(v___x_314_) == 0)
{
uint8_t v___x_315_; 
v___x_315_ = lean_unbox(v_defValue_312_);
return v___x_315_;
}
else
{
lean_object* v_val_316_; 
v_val_316_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_316_);
lean_dec_ref(v___x_314_);
if (lean_obj_tag(v_val_316_) == 1)
{
uint8_t v_v_317_; 
v_v_317_ = lean_ctor_get_uint8(v_val_316_, 0);
lean_dec_ref(v_val_316_);
return v_v_317_;
}
else
{
uint8_t v___x_318_; 
lean_dec(v_val_316_);
v___x_318_ = lean_unbox(v_defValue_312_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_319_, lean_object* v_opt_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_319_, v_opt_320_);
lean_dec_ref(v_opt_320_);
lean_dec_ref(v_opts_319_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_327_ = l_Lean_MessageData_ofFormat(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_328_, lean_object* v_macroStack_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_options_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_options_332_ = lean_ctor_get(v___y_330_, 2);
v___x_333_ = l_Lean_Elab_pp_macroStack;
v___x_334_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_macroStack_329_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_msgData_328_);
return v___x_335_;
}
else
{
if (lean_obj_tag(v_macroStack_329_) == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_msgData_328_);
return v___x_336_;
}
else
{
lean_object* v_head_337_; lean_object* v_after_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_353_; 
v_head_337_ = lean_ctor_get(v_macroStack_329_, 0);
lean_inc(v_head_337_);
v_after_338_ = lean_ctor_get(v_head_337_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_head_337_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v_head_337_, 0);
lean_dec(v_unused_354_);
v___x_340_ = v_head_337_;
v_isShared_341_ = v_isSharedCheck_353_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_after_338_);
lean_dec(v_head_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_353_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 7);
lean_ctor_set(v___x_340_, 1, v___x_342_);
lean_ctor_set(v___x_340_, 0, v_msgData_328_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_msgData_328_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_352_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_msgData_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_345_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_MessageData_ofSyntax(v_after_338_);
v___x_348_ = l_Lean_indentD(v___x_347_);
v_msgData_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_349_, 0, v___x_346_);
lean_ctor_set(v_msgData_349_, 1, v___x_348_);
v___x_350_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_349_, v_macroStack_329_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_355_, lean_object* v_macroStack_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_355_, v_macroStack_356_, v___y_357_);
lean_dec_ref(v___y_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_ref_368_; lean_object* v___x_369_; lean_object* v_a_370_; lean_object* v_macroStack_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_ref_368_ = lean_ctor_get(v___y_365_, 5);
v___x_369_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_360_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_369_);
v_macroStack_371_ = lean_ctor_get(v___y_361_, 1);
v___x_372_ = l_Lean_Elab_getBetterRef(v_ref_368_, v_macroStack_371_);
lean_inc(v_macroStack_371_);
v___x_373_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_370_, v_macroStack_371_, v___y_365_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_372_);
lean_ctor_set(v___x_378_, 1, v_a_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 1);
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_392_, size_t v_i_393_, size_t v_stop_394_, lean_object* v_b_395_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_eq(v_i_393_, v_stop_394_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; size_t v___x_399_; size_t v___x_400_; 
v___x_397_ = lean_array_uget_borrowed(v_as_392_, v_i_393_);
lean_inc(v___x_397_);
v___x_398_ = l_Lean_NameSet_insert(v_b_395_, v___x_397_);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_add(v_i_393_, v___x_399_);
v_i_393_ = v___x_400_;
v_b_395_ = v___x_398_;
goto _start;
}
else
{
return v_b_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_, lean_object* v_b_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_stop_boxed_407_; lean_object* v_res_408_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_407_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_402_, v_i_boxed_406_, v_stop_boxed_407_, v_b_405_);
lean_dec_ref(v_as_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_409_, size_t v_i_410_, lean_object* v_bs_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_lt(v_i_410_, v_sz_409_);
if (v___x_412_ == 0)
{
return v_bs_411_;
}
else
{
lean_object* v_v_413_; lean_object* v___x_414_; lean_object* v_bs_x27_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v_v_413_ = lean_array_uget(v_bs_411_, v_i_410_);
v___x_414_ = lean_unsigned_to_nat(0u);
v_bs_x27_415_ = lean_array_uset(v_bs_411_, v_i_410_, v___x_414_);
v___x_416_ = l_Lean_TSyntax_getId(v_v_413_);
lean_dec(v_v_413_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_410_, v___x_417_);
v___x_419_ = lean_array_uset(v_bs_x27_415_, v_i_410_, v___x_416_);
v_i_410_ = v___x_418_;
v_bs_411_ = v___x_419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_421_, lean_object* v_i_422_, lean_object* v_bs_423_){
_start:
{
size_t v_sz_boxed_424_; size_t v_i_boxed_425_; lean_object* v_res_426_; 
v_sz_boxed_424_ = lean_unbox_usize(v_sz_421_);
lean_dec(v_sz_421_);
v_i_boxed_425_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_424_, v_i_boxed_425_, v_bs_423_);
return v_res_426_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_435_, size_t v_i_436_, lean_object* v_bs_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = lean_usize_dec_lt(v_i_436_, v_sz_435_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_bs_437_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v_bs_x27_441_; lean_object* v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v_bs_x27_441_ = lean_array_uset(v_bs_437_, v_i_436_, v___x_440_);
v___x_442_ = lean_box(0);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = lean_usize_add(v_i_436_, v___x_443_);
v___x_445_ = lean_array_uset(v_bs_x27_441_, v_i_436_, v___x_442_);
v_i_436_ = v___x_444_;
v_bs_437_ = v___x_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_447_, lean_object* v_i_448_, lean_object* v_bs_449_){
_start:
{
size_t v_sz_boxed_450_; size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_sz_boxed_450_ = lean_unbox_usize(v_sz_447_);
lean_dec(v_sz_447_);
v_i_boxed_451_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_450_, v_i_boxed_451_, v_bs_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_453_, uint8_t v___x_454_, lean_object* v_as_455_, size_t v_i_456_, size_t v_stop_457_, lean_object* v_b_458_){
_start:
{
lean_object* v___y_460_; uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_eq(v_i_456_, v_stop_457_);
if (v___x_464_ == 0)
{
lean_object* v_fst_465_; uint8_t v___x_466_; 
v_fst_465_ = lean_ctor_get(v_b_458_, 0);
v___x_466_ = lean_unbox(v_fst_465_);
if (v___x_466_ == 0)
{
lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_snd_467_ = lean_ctor_get(v_b_458_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_b_458_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_b_458_, 0);
lean_dec(v_unused_476_);
v___x_469_ = v_b_458_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_dec(v_b_458_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_box(v___x_453_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_snd_467_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
v___y_460_ = v___x_473_;
goto v___jp_459_;
}
}
}
else
{
lean_object* v_snd_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_snd_477_ = lean_ctor_get(v_b_458_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_b_458_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_b_458_, 0);
lean_dec(v_unused_488_);
v___x_479_ = v_b_458_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snd_477_);
lean_dec(v_b_458_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_481_ = lean_array_uget_borrowed(v_as_455_, v_i_456_);
lean_inc(v___x_481_);
v___x_482_ = lean_array_push(v_snd_477_, v___x_481_);
v___x_483_ = lean_box(v___x_454_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_482_);
lean_ctor_set(v___x_479_, 0, v___x_483_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_482_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v___y_460_ = v___x_485_;
goto v___jp_459_;
}
}
}
}
else
{
return v_b_458_;
}
v___jp_459_:
{
size_t v___x_461_; size_t v___x_462_; 
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_456_, v___x_461_);
v_i_456_ = v___x_462_;
v_b_458_ = v___y_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_, lean_object* v_b_494_){
_start:
{
uint8_t v___x_286225__boxed_495_; uint8_t v___x_286226__boxed_496_; size_t v_i_boxed_497_; size_t v_stop_boxed_498_; lean_object* v_res_499_; 
v___x_286225__boxed_495_ = lean_unbox(v___x_489_);
v___x_286226__boxed_496_ = lean_unbox(v___x_490_);
v_i_boxed_497_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_498_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_286225__boxed_495_, v___x_286226__boxed_496_, v_as_491_, v_i_boxed_497_, v_stop_boxed_498_, v_b_494_);
lean_dec_ref(v_as_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_500_, lean_object* v_declName_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v___x_504_; lean_object* v_env_505_; lean_object* v___x_506_; uint8_t v___x_507_; uint8_t v___x_508_; 
v___x_504_ = 0;
v_env_505_ = l_Lean_Environment_setExporting(v_env_500_, v___x_504_);
lean_inc(v_declName_501_);
v___x_506_ = l_Lean_mkPrivateName(v_env_505_, v_declName_501_);
v___x_507_ = 1;
lean_inc_ref(v_env_505_);
v___x_508_ = l_Lean_Environment_contains(v_env_505_, v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_509_ = l_Lean_privateToUserName(v_declName_501_);
v___x_510_ = l_Lean_Environment_contains(v_env_505_, v___x_509_, v___x_507_);
v___x_511_ = lean_box(v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___y_503_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec_ref(v_env_505_);
lean_dec(v_declName_501_);
v___x_513_ = lean_box(v___x_508_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___y_503_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_515_, lean_object* v_declName_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_515_, v_declName_516_, v___y_517_, v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = l_Lean_maxRecDepthErrorMessage;
v___x_526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_528_ = l_Lean_MessageData_ofFormat(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_530_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_531_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_532_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_ref_532_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_540_, lean_object* v___y_541_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_a_542_);
v___x_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_543_, 0, v_a_542_);
lean_ctor_set(v___x_543_, 1, v___y_541_);
return v___x_543_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_a_544_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v_a_544_);
lean_ctor_set(v___x_545_, 1, v___y_541_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_546_, v___y_547_);
lean_dec_ref(v_x_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_549_, lean_object* v_stx_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_549_, v_stx_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
if (lean_obj_tag(v_a_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_a_555_ = lean_ctor_get(v___x_553_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_553_, 0);
lean_dec(v_unused_564_);
v___x_557_ = v___x_553_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_a_555_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_593_; 
v_val_565_ = lean_ctor_get(v_a_554_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_593_ == 0)
{
v___x_567_ = v_a_554_;
v_isShared_568_ = v_isSharedCheck_593_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v_a_554_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_593_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_snd_569_; 
v_snd_569_ = lean_ctor_get(v_val_565_, 1);
lean_inc(v_snd_569_);
lean_dec(v_val_565_);
if (lean_obj_tag(v_snd_569_) == 0)
{
lean_object* v_a_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
lean_del_object(v___x_567_);
v_a_570_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_a_570_);
lean_dec_ref(v___x_553_);
v_a_571_ = lean_ctor_get(v_snd_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_snd_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_snd_569_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v_snd_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_576_, v_a_570_);
lean_dec_ref(v___x_576_);
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_592_; 
v_a_580_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_a_580_);
lean_dec_ref(v___x_553_);
v_a_581_ = lean_ctor_get(v_snd_569_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_snd_569_);
if (v_isSharedCheck_592_ == 0)
{
v___x_583_ = v_snd_569_;
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v_snd_569_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_a_581_);
v___x_586_ = v___x_567_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_591_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_588_, v_a_580_);
lean_dec_ref(v___x_588_);
return v___x_589_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_594_ = lean_ctor_get(v___x_553_, 0);
v_a_595_ = lean_ctor_get(v___x_553_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_553_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_inc(v_a_594_);
lean_dec(v___x_553_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_603_, lean_object* v_stx_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_603_, v_stx_604_, v___y_605_, v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_fileName_617_; lean_object* v_fileMap_618_; lean_object* v_options_619_; lean_object* v_currRecDepth_620_; lean_object* v_maxRecDepth_621_; lean_object* v_ref_622_; lean_object* v_currNamespace_623_; lean_object* v_openDecls_624_; lean_object* v_initHeartbeats_625_; lean_object* v_maxHeartbeats_626_; lean_object* v_quotContext_627_; lean_object* v_currMacroScope_628_; uint8_t v_diag_629_; lean_object* v_cancelTk_x3f_630_; uint8_t v_suppressElabErrors_631_; lean_object* v_inheritedTraceOptions_632_; lean_object* v_ref_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_fileName_617_ = lean_ctor_get(v___y_614_, 0);
v_fileMap_618_ = lean_ctor_get(v___y_614_, 1);
v_options_619_ = lean_ctor_get(v___y_614_, 2);
v_currRecDepth_620_ = lean_ctor_get(v___y_614_, 3);
v_maxRecDepth_621_ = lean_ctor_get(v___y_614_, 4);
v_ref_622_ = lean_ctor_get(v___y_614_, 5);
v_currNamespace_623_ = lean_ctor_get(v___y_614_, 6);
v_openDecls_624_ = lean_ctor_get(v___y_614_, 7);
v_initHeartbeats_625_ = lean_ctor_get(v___y_614_, 8);
v_maxHeartbeats_626_ = lean_ctor_get(v___y_614_, 9);
v_quotContext_627_ = lean_ctor_get(v___y_614_, 10);
v_currMacroScope_628_ = lean_ctor_get(v___y_614_, 11);
v_diag_629_ = lean_ctor_get_uint8(v___y_614_, sizeof(void*)*14);
v_cancelTk_x3f_630_ = lean_ctor_get(v___y_614_, 12);
v_suppressElabErrors_631_ = lean_ctor_get_uint8(v___y_614_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_632_ = lean_ctor_get(v___y_614_, 13);
v_ref_633_ = l_Lean_replaceRef(v_ref_608_, v_ref_622_);
lean_inc_ref(v_inheritedTraceOptions_632_);
lean_inc(v_cancelTk_x3f_630_);
lean_inc(v_currMacroScope_628_);
lean_inc(v_quotContext_627_);
lean_inc(v_maxHeartbeats_626_);
lean_inc(v_initHeartbeats_625_);
lean_inc(v_openDecls_624_);
lean_inc(v_currNamespace_623_);
lean_inc(v_maxRecDepth_621_);
lean_inc(v_currRecDepth_620_);
lean_inc_ref(v_options_619_);
lean_inc_ref(v_fileMap_618_);
lean_inc_ref(v_fileName_617_);
v___x_634_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_634_, 0, v_fileName_617_);
lean_ctor_set(v___x_634_, 1, v_fileMap_618_);
lean_ctor_set(v___x_634_, 2, v_options_619_);
lean_ctor_set(v___x_634_, 3, v_currRecDepth_620_);
lean_ctor_set(v___x_634_, 4, v_maxRecDepth_621_);
lean_ctor_set(v___x_634_, 5, v_ref_633_);
lean_ctor_set(v___x_634_, 6, v_currNamespace_623_);
lean_ctor_set(v___x_634_, 7, v_openDecls_624_);
lean_ctor_set(v___x_634_, 8, v_initHeartbeats_625_);
lean_ctor_set(v___x_634_, 9, v_maxHeartbeats_626_);
lean_ctor_set(v___x_634_, 10, v_quotContext_627_);
lean_ctor_set(v___x_634_, 11, v_currMacroScope_628_);
lean_ctor_set(v___x_634_, 12, v_cancelTk_x3f_630_);
lean_ctor_set(v___x_634_, 13, v_inheritedTraceOptions_632_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*14, v_diag_629_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*14 + 1, v_suppressElabErrors_631_);
v___x_635_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___x_634_, v___y_615_);
lean_dec_ref(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_636_, v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v_ref_636_);
return v_res_645_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_646_; double v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_float_of_nat(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_ref_658_; lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_704_; 
v_ref_658_ = lean_ctor_get(v___y_655_, 5);
v___x_659_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_704_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_704_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_704_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v_traceState_665_; lean_object* v_env_666_; lean_object* v_nextMacroScope_667_; lean_object* v_ngen_668_; lean_object* v_auxDeclNGen_669_; lean_object* v_cache_670_; lean_object* v_messages_671_; lean_object* v_infoState_672_; lean_object* v_snapshotTasks_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_703_; 
v___x_664_ = lean_st_ref_take(v___y_656_);
v_traceState_665_ = lean_ctor_get(v___x_664_, 4);
v_env_666_ = lean_ctor_get(v___x_664_, 0);
v_nextMacroScope_667_ = lean_ctor_get(v___x_664_, 1);
v_ngen_668_ = lean_ctor_get(v___x_664_, 2);
v_auxDeclNGen_669_ = lean_ctor_get(v___x_664_, 3);
v_cache_670_ = lean_ctor_get(v___x_664_, 5);
v_messages_671_ = lean_ctor_get(v___x_664_, 6);
v_infoState_672_ = lean_ctor_get(v___x_664_, 7);
v_snapshotTasks_673_ = lean_ctor_get(v___x_664_, 8);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_703_ == 0)
{
v___x_675_ = v___x_664_;
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snapshotTasks_673_);
lean_inc(v_infoState_672_);
lean_inc(v_messages_671_);
lean_inc(v_cache_670_);
lean_inc(v_traceState_665_);
lean_inc(v_auxDeclNGen_669_);
lean_inc(v_ngen_668_);
lean_inc(v_nextMacroScope_667_);
lean_inc(v_env_666_);
lean_dec(v___x_664_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
uint64_t v_tid_677_; lean_object* v_traces_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_702_; 
v_tid_677_ = lean_ctor_get_uint64(v_traceState_665_, sizeof(void*)*1);
v_traces_678_ = lean_ctor_get(v_traceState_665_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_traceState_665_);
if (v_isSharedCheck_702_ == 0)
{
v___x_680_ = v_traceState_665_;
v_isShared_681_ = v_isSharedCheck_702_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_traces_678_);
lean_dec(v_traceState_665_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_702_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; double v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_682_ = lean_box(0);
v___x_683_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_684_ = 0;
v___x_685_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_686_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_686_, 0, v_cls_651_);
lean_ctor_set(v___x_686_, 1, v___x_682_);
lean_ctor_set(v___x_686_, 2, v___x_685_);
lean_ctor_set_float(v___x_686_, sizeof(void*)*3, v___x_683_);
lean_ctor_set_float(v___x_686_, sizeof(void*)*3 + 8, v___x_683_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3 + 16, v___x_684_);
v___x_687_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_688_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v_a_660_);
lean_ctor_set(v___x_688_, 2, v___x_687_);
lean_inc(v_ref_658_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_ref_658_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_PersistentArray_push___redArg(v_traces_678_, v___x_689_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_690_);
v___x_692_ = v___x_680_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_690_);
lean_ctor_set_uint64(v_reuseFailAlloc_701_, sizeof(void*)*1, v_tid_677_);
v___x_692_ = v_reuseFailAlloc_701_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 4, v___x_692_);
v___x_694_ = v___x_675_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_env_666_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_nextMacroScope_667_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_ngen_668_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_auxDeclNGen_669_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_cache_670_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_messages_671_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_infoState_672_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_snapshotTasks_673_);
v___x_694_ = v_reuseFailAlloc_700_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = lean_st_ref_set(v___y_656_, v___x_694_);
v___x_696_ = lean_box(0);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_696_);
v___x_698_ = v___x_662_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_705_, v_msg_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
if (lean_obj_tag(v_as_716_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v_options_726_; uint8_t v_hasTrace_727_; 
v_options_726_ = lean_ctor_get(v___y_721_, 2);
v_hasTrace_727_ = lean_ctor_get_uint8(v_options_726_, sizeof(void*)*1);
if (v_hasTrace_727_ == 0)
{
lean_object* v_tail_728_; 
v_tail_728_ = lean_ctor_get(v_as_716_, 1);
lean_inc(v_tail_728_);
lean_dec_ref(v_as_716_);
v_as_716_ = v_tail_728_;
goto _start;
}
else
{
lean_object* v_head_730_; lean_object* v_tail_731_; lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v_inheritedTraceOptions_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_head_730_ = lean_ctor_get(v_as_716_, 0);
lean_inc(v_head_730_);
v_tail_731_ = lean_ctor_get(v_as_716_, 1);
lean_inc(v_tail_731_);
lean_dec_ref(v_as_716_);
v_fst_732_ = lean_ctor_get(v_head_730_, 0);
lean_inc_n(v_fst_732_, 2);
v_snd_733_ = lean_ctor_get(v_head_730_, 1);
lean_inc(v_snd_733_);
lean_dec(v_head_730_);
v_inheritedTraceOptions_734_ = lean_ctor_get(v___y_721_, 13);
v___x_735_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_736_ = l_Lean_Name_append(v___x_735_, v_fst_732_);
v___x_737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_734_, v_options_726_, v___x_736_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_snd_733_);
lean_dec(v_fst_732_);
v_as_716_ = v_tail_731_;
goto _start;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_739_, 0, v_snd_733_);
v___x_740_ = l_Lean_MessageData_ofFormat(v___x_739_);
v___x_741_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_732_, v___x_740_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_dec_ref(v___x_741_);
v_as_716_ = v_tail_731_;
goto _start;
}
else
{
lean_dec(v_tail_731_);
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(0);
return v___x_754_;
}
else
{
lean_object* v_key_755_; lean_object* v_value_756_; lean_object* v_tail_757_; uint8_t v___x_758_; 
v_key_755_ = lean_ctor_get(v_x_753_, 0);
v_value_756_ = lean_ctor_get(v_x_753_, 1);
v_tail_757_ = lean_ctor_get(v_x_753_, 2);
v___x_758_ = lean_name_eq(v_key_755_, v_a_752_);
if (v___x_758_ == 0)
{
v_x_753_ = v_tail_757_;
goto _start;
}
else
{
lean_object* v___x_760_; 
lean_inc(v_value_756_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v_value_756_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_761_, lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_761_, v_x_762_);
lean_dec(v_x_762_);
lean_dec(v_a_761_);
return v_res_763_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_764_; uint64_t v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(1723u);
v___x_765_ = lean_uint64_of_nat(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_buckets_768_; lean_object* v___x_769_; uint64_t v___y_771_; 
v_buckets_768_ = lean_ctor_get(v_m_766_, 1);
v___x_769_ = lean_array_get_size(v_buckets_768_);
if (lean_obj_tag(v_a_767_) == 0)
{
uint64_t v___x_785_; 
v___x_785_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_771_ = v___x_785_;
goto v___jp_770_;
}
else
{
uint64_t v_hash_786_; 
v_hash_786_ = lean_ctor_get_uint64(v_a_767_, sizeof(void*)*2);
v___y_771_ = v_hash_786_;
goto v___jp_770_;
}
v___jp_770_:
{
uint64_t v___x_772_; uint64_t v___x_773_; uint64_t v_fold_774_; uint64_t v___x_775_; uint64_t v___x_776_; uint64_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_772_ = 32ULL;
v___x_773_ = lean_uint64_shift_right(v___y_771_, v___x_772_);
v_fold_774_ = lean_uint64_xor(v___y_771_, v___x_773_);
v___x_775_ = 16ULL;
v___x_776_ = lean_uint64_shift_right(v_fold_774_, v___x_775_);
v___x_777_ = lean_uint64_xor(v_fold_774_, v___x_776_);
v___x_778_ = lean_uint64_to_usize(v___x_777_);
v___x_779_ = lean_usize_of_nat(v___x_769_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_sub(v___x_779_, v___x_780_);
v___x_782_ = lean_usize_land(v___x_778_, v___x_781_);
v___x_783_ = lean_array_uget_borrowed(v_buckets_768_, v___x_782_);
v___x_784_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_767_, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_m_787_);
return v_res_789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_790_, lean_object* v_i_791_, lean_object* v_k_792_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_keys_790_);
v___x_794_ = lean_nat_dec_lt(v_i_791_, v___x_793_);
if (v___x_794_ == 0)
{
lean_dec(v_i_791_);
return v___x_794_;
}
else
{
lean_object* v_k_x27_795_; uint8_t v___x_796_; 
v_k_x27_795_ = lean_array_fget_borrowed(v_keys_790_, v_i_791_);
v___x_796_ = l_Lean_instBEqExtraModUse_beq(v_k_792_, v_k_x27_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v_i_791_, v___x_797_);
lean_dec(v_i_791_);
v_i_791_ = v___x_798_;
goto _start;
}
else
{
lean_dec(v_i_791_);
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_800_, lean_object* v_i_801_, lean_object* v_k_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_800_, v_i_801_, v_k_802_);
lean_dec_ref(v_k_802_);
lean_dec_ref(v_keys_800_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_805_; size_t v___x_806_; size_t v___x_807_; 
v___x_805_ = ((size_t)5ULL);
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_shift_left(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; 
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0);
v___x_810_ = lean_usize_sub(v___x_809_, v___x_808_);
return v___x_810_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_811_, size_t v_x_812_, lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v_es_814_; lean_object* v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v_j_819_; lean_object* v___x_820_; 
v_es_814_ = lean_ctor_get(v_x_811_, 0);
v___x_815_ = lean_box(2);
v___x_816_ = ((size_t)5ULL);
v___x_817_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1);
v___x_818_ = lean_usize_land(v_x_812_, v___x_817_);
v_j_819_ = lean_usize_to_nat(v___x_818_);
v___x_820_ = lean_array_get_borrowed(v___x_815_, v_es_814_, v_j_819_);
lean_dec(v_j_819_);
switch(lean_obj_tag(v___x_820_))
{
case 0:
{
lean_object* v_key_821_; uint8_t v___x_822_; 
v_key_821_ = lean_ctor_get(v___x_820_, 0);
v___x_822_ = l_Lean_instBEqExtraModUse_beq(v_x_813_, v_key_821_);
return v___x_822_;
}
case 1:
{
lean_object* v_node_823_; size_t v___x_824_; 
v_node_823_ = lean_ctor_get(v___x_820_, 0);
v___x_824_ = lean_usize_shift_right(v_x_812_, v___x_816_);
v_x_811_ = v_node_823_;
v_x_812_ = v___x_824_;
goto _start;
}
default: 
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
}
}
else
{
lean_object* v_ks_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_ks_827_ = lean_ctor_get(v_x_811_, 0);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_827_, v___x_828_, v_x_813_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
size_t v_x_286755__boxed_833_; uint8_t v_res_834_; lean_object* v_r_835_; 
v_x_286755__boxed_833_ = lean_unbox_usize(v_x_831_);
lean_dec(v_x_831_);
v_res_834_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_830_, v_x_286755__boxed_833_, v_x_832_);
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_830_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint64_t v___x_838_; size_t v___x_839_; uint8_t v___x_840_; 
v___x_838_ = l_Lean_instHashableExtraModUse_hash(v_x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_836_, v___x_839_, v_x_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_841_, v_x_842_);
lean_dec_ref(v_x_842_);
lean_dec_ref(v_x_841_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_848_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_849_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_848_, v___x_847_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_850_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_856_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
lean_ctor_set(v___x_856_, 4, v___x_855_);
lean_ctor_set(v___x_856_, 5, v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_cls_868_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_869_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_870_ = l_Lean_Name_append(v___x_869_, v_cls_868_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_881_, uint8_t v_isMeta_882_, lean_object* v_hint_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_env_892_; uint8_t v_isExporting_893_; lean_object* v___x_894_; lean_object* v_env_895_; lean_object* v___x_896_; lean_object* v_entry_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_891_ = lean_st_ref_get(v___y_889_);
v_env_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_env_892_);
lean_dec(v___x_891_);
v_isExporting_893_ = lean_ctor_get_uint8(v_env_892_, sizeof(void*)*8);
lean_dec_ref(v_env_892_);
v___x_894_ = lean_st_ref_get(v___y_889_);
v_env_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_env_895_);
lean_dec(v___x_894_);
v___x_896_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_881_);
v_entry_897_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_897_, 0, v_mod_881_);
lean_ctor_set_uint8(v_entry_897_, sizeof(void*)*1, v_isExporting_893_);
lean_ctor_set_uint8(v_entry_897_, sizeof(void*)*1 + 1, v_isMeta_882_);
v___x_898_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_899_ = lean_box(1);
v___x_900_ = lean_box(0);
v___x_943_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_896_, v___x_898_, v_env_895_, v___x_899_, v___x_900_);
v___x_944_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_943_, v_entry_897_);
lean_dec(v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v_options_945_; uint8_t v_hasTrace_946_; 
v_options_945_ = lean_ctor_get(v___y_888_, 2);
v_hasTrace_946_ = lean_ctor_get_uint8(v_options_945_, sizeof(void*)*1);
if (v_hasTrace_946_ == 0)
{
lean_dec(v_hint_883_);
lean_dec(v_mod_881_);
v___y_902_ = v___y_887_;
v___y_903_ = v___y_889_;
goto v___jp_901_;
}
else
{
lean_object* v_inheritedTraceOptions_947_; lean_object* v_cls_948_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_inheritedTraceOptions_947_ = lean_ctor_get(v___y_888_, 13);
v_cls_948_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_968_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_947_, v_options_945_, v___x_968_);
if (v___x_969_ == 0)
{
lean_dec(v_hint_883_);
lean_dec(v_mod_881_);
v___y_902_ = v___y_887_;
v___y_903_ = v___y_889_;
goto v___jp_901_;
}
else
{
lean_object* v___x_970_; lean_object* v___y_972_; 
v___x_970_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_893_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_972_ = v___x_979_;
goto v___jp_971_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_972_ = v___x_980_;
goto v___jp_971_;
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_inc_ref(v___y_972_);
v___x_973_ = l_Lean_stringToMessageData(v___y_972_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_970_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
if (v_isMeta_882_ == 0)
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_955_ = v___x_976_;
v___y_956_ = v___x_977_;
goto v___jp_954_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_955_ = v___x_976_;
v___y_956_ = v___x_978_;
goto v___jp_954_;
}
}
}
v___jp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___y_950_);
lean_ctor_set(v___x_952_, 1, v___y_951_);
v___x_953_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_948_, v___x_952_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec_ref(v___x_953_);
v___y_902_ = v___y_887_;
v___y_903_ = v___y_889_;
goto v___jp_901_;
}
else
{
lean_dec_ref(v_entry_897_);
return v___x_953_;
}
}
v___jp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
lean_inc_ref(v___y_956_);
v___x_957_ = l_Lean_stringToMessageData(v___y_956_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_955_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Lean_MessageData_ofName(v_mod_881_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_Name_isAnonymous(v_hint_883_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_965_ = l_Lean_MessageData_ofName(v_hint_883_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___y_950_ = v___x_962_;
v___y_951_ = v___x_966_;
goto v___jp_949_;
}
else
{
lean_object* v___x_967_; 
lean_dec(v_hint_883_);
v___x_967_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_950_ = v___x_962_;
v___y_951_ = v___x_967_;
goto v___jp_949_;
}
}
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref(v_entry_897_);
lean_dec(v_hint_883_);
lean_dec(v_mod_881_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
v___jp_901_:
{
lean_object* v___x_904_; lean_object* v_toEnvExtension_905_; lean_object* v_env_906_; lean_object* v_nextMacroScope_907_; lean_object* v_ngen_908_; lean_object* v_auxDeclNGen_909_; lean_object* v_traceState_910_; lean_object* v_messages_911_; lean_object* v_infoState_912_; lean_object* v_snapshotTasks_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_941_; 
v___x_904_ = lean_st_ref_take(v___y_903_);
v_toEnvExtension_905_ = lean_ctor_get(v___x_898_, 0);
v_env_906_ = lean_ctor_get(v___x_904_, 0);
v_nextMacroScope_907_ = lean_ctor_get(v___x_904_, 1);
v_ngen_908_ = lean_ctor_get(v___x_904_, 2);
v_auxDeclNGen_909_ = lean_ctor_get(v___x_904_, 3);
v_traceState_910_ = lean_ctor_get(v___x_904_, 4);
v_messages_911_ = lean_ctor_get(v___x_904_, 6);
v_infoState_912_ = lean_ctor_get(v___x_904_, 7);
v_snapshotTasks_913_ = lean_ctor_get(v___x_904_, 8);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_904_, 5);
lean_dec(v_unused_942_);
v___x_915_ = v___x_904_;
v_isShared_916_ = v_isSharedCheck_941_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snapshotTasks_913_);
lean_inc(v_infoState_912_);
lean_inc(v_messages_911_);
lean_inc(v_traceState_910_);
lean_inc(v_auxDeclNGen_909_);
lean_inc(v_ngen_908_);
lean_inc(v_nextMacroScope_907_);
lean_inc(v_env_906_);
lean_dec(v___x_904_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_941_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_asyncMode_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_asyncMode_917_ = lean_ctor_get(v_toEnvExtension_905_, 2);
v___x_918_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_898_, v_env_906_, v_entry_897_, v_asyncMode_917_, v___x_900_);
v___x_919_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 5, v___x_919_);
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_nextMacroScope_907_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_ngen_908_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_auxDeclNGen_909_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_traceState_910_);
lean_ctor_set(v_reuseFailAlloc_940_, 5, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_940_, 6, v_messages_911_);
lean_ctor_set(v_reuseFailAlloc_940_, 7, v_infoState_912_);
lean_ctor_set(v_reuseFailAlloc_940_, 8, v_snapshotTasks_913_);
v___x_921_ = v_reuseFailAlloc_940_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_mctx_924_; lean_object* v_zetaDeltaFVarIds_925_; lean_object* v_postponed_926_; lean_object* v_diag_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_938_; 
v___x_922_ = lean_st_ref_set(v___y_903_, v___x_921_);
v___x_923_ = lean_st_ref_take(v___y_902_);
v_mctx_924_ = lean_ctor_get(v___x_923_, 0);
v_zetaDeltaFVarIds_925_ = lean_ctor_get(v___x_923_, 2);
v_postponed_926_ = lean_ctor_get(v___x_923_, 3);
v_diag_927_ = lean_ctor_get(v___x_923_, 4);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_923_, 1);
lean_dec(v_unused_939_);
v___x_929_ = v___x_923_;
v_isShared_930_ = v_isSharedCheck_938_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_diag_927_);
lean_inc(v_postponed_926_);
lean_inc(v_zetaDeltaFVarIds_925_);
lean_inc(v_mctx_924_);
lean_dec(v___x_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_938_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_mctx_924_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_zetaDeltaFVarIds_925_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_postponed_926_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_diag_927_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_st_ref_set(v___y_902_, v___x_933_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_983_, lean_object* v_isMeta_984_, lean_object* v_hint_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v_isMeta_boxed_993_; lean_object* v_res_994_; 
v_isMeta_boxed_993_ = lean_unbox(v_isMeta_984_);
v_res_994_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_983_, v_isMeta_boxed_993_, v_hint_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_995_, lean_object* v_declName_996_, lean_object* v_as_997_, size_t v_sz_998_, size_t v_i_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_lt(v_i_999_, v_sz_998_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec(v_declName_996_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_b_1000_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v_modules_1011_; lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v_toImport_1015_; lean_object* v_module_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1010_ = l_Lean_Environment_header(v___x_995_);
v_modules_1011_ = lean_ctor_get(v___x_1010_, 3);
lean_inc_ref(v_modules_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1013_ = lean_array_uget_borrowed(v_as_997_, v_i_999_);
v___x_1014_ = lean_array_get(v___x_1012_, v_modules_1011_, v_a_1013_);
lean_dec_ref(v_modules_1011_);
v_toImport_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_ref(v_toImport_1015_);
lean_dec(v___x_1014_);
v_module_1016_ = lean_ctor_get(v_toImport_1015_, 0);
lean_inc(v_module_1016_);
lean_dec_ref(v_toImport_1015_);
v___x_1017_ = 0;
lean_inc(v_declName_996_);
v___x_1018_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1016_, v___x_1017_, v_declName_996_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; 
lean_dec_ref(v___x_1018_);
v___x_1019_ = lean_box(0);
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_999_, v___x_1020_);
v_i_999_ = v___x_1021_;
v_b_1000_ = v___x_1019_;
goto _start;
}
else
{
lean_dec(v_declName_996_);
return v___x_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1023_, lean_object* v_declName_1024_, lean_object* v_as_1025_, lean_object* v_sz_1026_, lean_object* v_i_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1026_);
lean_dec(v_sz_1026_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1027_);
lean_dec(v_i_1027_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1023_, v_declName_1024_, v_as_1025_, v_sz_boxed_1036_, v_i_boxed_1037_, v_b_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec_ref(v_as_1025_);
lean_dec_ref(v___x_1023_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1042_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1043_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1042_, v___x_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1046_, uint8_t v_isMeta_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v_env_1059_; lean_object* v___y_1061_; lean_object* v___x_1074_; 
v___x_1055_ = lean_st_ref_get(v___y_1053_);
v_env_1059_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1059_);
lean_dec(v___x_1055_);
v___x_1074_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1059_, v_declName_1046_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_dec_ref(v_env_1059_);
lean_dec(v_declName_1046_);
goto v___jp_1056_;
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1076_; lean_object* v_modules_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l_Lean_Environment_header(v_env_1059_);
v_modules_1077_ = lean_ctor_get(v___x_1076_, 3);
lean_inc_ref(v_modules_1077_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_array_get_size(v_modules_1077_);
v___x_1079_ = lean_nat_dec_lt(v_val_1075_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_modules_1077_);
lean_dec(v_val_1075_);
lean_dec_ref(v_env_1059_);
lean_dec(v_declName_1046_);
goto v___jp_1056_;
}
else
{
lean_object* v___x_1080_; lean_object* v_env_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___y_1085_; 
v___x_1080_ = lean_st_ref_get(v___y_1053_);
v_env_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_ref(v_env_1081_);
lean_dec(v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1083_ = lean_array_fget(v_modules_1077_, v_val_1075_);
lean_dec(v_val_1075_);
lean_dec_ref(v_modules_1077_);
if (v_isMeta_1047_ == 0)
{
lean_dec_ref(v_env_1081_);
v___y_1085_ = v_isMeta_1047_;
goto v___jp_1084_;
}
else
{
uint8_t v___x_1096_; 
lean_inc(v_declName_1046_);
v___x_1096_ = l_Lean_isMarkedMeta(v_env_1081_, v_declName_1046_);
if (v___x_1096_ == 0)
{
v___y_1085_ = v_isMeta_1047_;
goto v___jp_1084_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = 0;
v___y_1085_ = v___x_1097_;
goto v___jp_1084_;
}
}
v___jp_1084_:
{
lean_object* v_toImport_1086_; lean_object* v_module_1087_; lean_object* v___x_1088_; 
v_toImport_1086_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_toImport_1086_);
lean_dec(v___x_1083_);
v_module_1087_ = lean_ctor_get(v_toImport_1086_, 0);
lean_inc(v_module_1087_);
lean_dec_ref(v_toImport_1086_);
lean_inc(v_declName_1046_);
v___x_1088_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1087_, v___y_1085_, v_declName_1046_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v___x_1088_);
v___x_1089_ = l_Lean_indirectModUseExt;
v___x_1090_ = lean_box(1);
v___x_1091_ = lean_box(0);
lean_inc_ref(v_env_1059_);
v___x_1092_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1082_, v___x_1089_, v_env_1059_, v___x_1090_, v___x_1091_);
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1092_, v_declName_1046_);
lean_dec(v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1061_ = v___x_1094_;
goto v___jp_1060_;
}
else
{
lean_object* v_val_1095_; 
v_val_1095_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1095_);
lean_dec_ref(v___x_1093_);
v___y_1061_ = v_val_1095_;
goto v___jp_1060_;
}
}
else
{
lean_dec_ref(v_env_1059_);
lean_dec(v_declName_1046_);
return v___x_1088_;
}
}
}
}
v___jp_1056_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; size_t v_sz_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_box(0);
v_sz_1063_ = lean_array_size(v___y_1061_);
v___x_1064_ = ((size_t)0ULL);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1059_, v_declName_1046_, v___y_1061_, v_sz_1063_, v___x_1064_, v___x_1062_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec_ref(v___y_1061_);
lean_dec_ref(v_env_1059_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___x_1065_, 0);
lean_dec(v_unused_1073_);
v___x_1067_ = v___x_1065_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_dec(v___x_1065_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1062_);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1062_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
else
{
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1098_, lean_object* v_isMeta_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
uint8_t v_isMeta_boxed_1107_; lean_object* v_res_1108_; 
v_isMeta_boxed_1107_ = lean_unbox(v_isMeta_1099_);
v_res_1108_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1098_, v_isMeta_boxed_1107_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1109_, lean_object* v_b_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
if (lean_obj_tag(v_as_x27_1109_) == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_b_1110_);
return v___x_1118_;
}
else
{
lean_object* v_head_1119_; lean_object* v_tail_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v_head_1119_ = lean_ctor_get(v_as_x27_1109_, 0);
v_tail_1120_ = lean_ctor_get(v_as_x27_1109_, 1);
v___x_1121_ = 1;
lean_inc(v_head_1119_);
v___x_1122_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1119_, v___x_1121_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1122_);
v___x_1123_ = lean_box(0);
v_as_x27_1109_ = v_tail_1120_;
v_b_1110_ = v___x_1123_;
goto _start;
}
else
{
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1125_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v_as_x27_1125_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1135_, lean_object* v_currNamespace_1136_, lean_object* v_openDecls_1137_, lean_object* v_n_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l_Lean_ResolveName_resolveNamespace(v_env_1135_, v_currNamespace_1136_, v_openDecls_1137_, v_n_1138_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___y_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1143_, lean_object* v_currNamespace_1144_, lean_object* v_openDecls_1145_, lean_object* v_n_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1143_, v_currNamespace_1144_, v_openDecls_1145_, v_n_1146_, v___y_1147_, v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_currNamespace_1150_);
lean_ctor_set(v___x_1153_, 1, v___y_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1154_, v___y_1155_, v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1158_, lean_object* v_options_1159_, lean_object* v_currNamespace_1160_, lean_object* v_openDecls_1161_, lean_object* v_n_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l_Lean_ResolveName_resolveGlobalName(v_env_1158_, v_options_1159_, v_currNamespace_1160_, v_openDecls_1161_, v_n_1162_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___y_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1167_, lean_object* v_options_1168_, lean_object* v_currNamespace_1169_, lean_object* v_openDecls_1170_, lean_object* v_n_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1167_, v_options_1168_, v_currNamespace_1169_, v_openDecls_1170_, v_n_1171_, v___y_1172_, v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec_ref(v_options_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v_env_1185_; lean_object* v_options_1186_; lean_object* v_currRecDepth_1187_; lean_object* v_maxRecDepth_1188_; lean_object* v_ref_1189_; lean_object* v_currNamespace_1190_; lean_object* v_openDecls_1191_; lean_object* v_quotContext_1192_; lean_object* v_currMacroScope_1193_; lean_object* v___x_1194_; lean_object* v_nextMacroScope_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v_methods_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1184_ = lean_st_ref_get(v___y_1182_);
v_env_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc_ref_n(v_env_1185_, 4);
lean_dec(v___x_1184_);
v_options_1186_ = lean_ctor_get(v___y_1181_, 2);
v_currRecDepth_1187_ = lean_ctor_get(v___y_1181_, 3);
v_maxRecDepth_1188_ = lean_ctor_get(v___y_1181_, 4);
v_ref_1189_ = lean_ctor_get(v___y_1181_, 5);
v_currNamespace_1190_ = lean_ctor_get(v___y_1181_, 6);
v_openDecls_1191_ = lean_ctor_get(v___y_1181_, 7);
v_quotContext_1192_ = lean_ctor_get(v___y_1181_, 10);
v_currMacroScope_1193_ = lean_ctor_get(v___y_1181_, 11);
v___x_1194_ = lean_st_ref_get(v___y_1182_);
v_nextMacroScope_1195_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_nextMacroScope_1195_);
lean_dec(v___x_1194_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1196_, 0, v_env_1185_);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1197_, 0, v_env_1185_);
lean_inc_n(v_openDecls_1191_, 2);
lean_inc_n(v_currNamespace_1190_, 3);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1198_, 0, v_env_1185_);
lean_closure_set(v___f_1198_, 1, v_currNamespace_1190_);
lean_closure_set(v___f_1198_, 2, v_openDecls_1191_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1199_, 0, v_currNamespace_1190_);
lean_inc_ref(v_options_1186_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1200_, 0, v_env_1185_);
lean_closure_set(v___f_1200_, 1, v_options_1186_);
lean_closure_set(v___f_1200_, 2, v_currNamespace_1190_);
lean_closure_set(v___f_1200_, 3, v_openDecls_1191_);
v_methods_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1201_, 0, v___f_1196_);
lean_ctor_set(v_methods_1201_, 1, v___f_1199_);
lean_ctor_set(v_methods_1201_, 2, v___f_1197_);
lean_ctor_set(v_methods_1201_, 3, v___f_1198_);
lean_ctor_set(v_methods_1201_, 4, v___f_1200_);
lean_inc(v_ref_1189_);
lean_inc(v_maxRecDepth_1188_);
lean_inc(v_currRecDepth_1187_);
lean_inc(v_currMacroScope_1193_);
lean_inc(v_quotContext_1192_);
v___x_1202_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1202_, 0, v_methods_1201_);
lean_ctor_set(v___x_1202_, 1, v_quotContext_1192_);
lean_ctor_set(v___x_1202_, 2, v_currMacroScope_1193_);
lean_ctor_set(v___x_1202_, 3, v_currRecDepth_1187_);
lean_ctor_set(v___x_1202_, 4, v_maxRecDepth_1188_);
lean_ctor_set(v___x_1202_, 5, v_ref_1189_);
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1204_, 0, v_nextMacroScope_1195_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
lean_ctor_set(v___x_1204_, 2, v___x_1203_);
v___x_1205_ = lean_apply_2(v_x_1176_, v___x_1202_, v___x_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v_a_1207_; lean_object* v_macroScope_1208_; lean_object* v_traceMsgs_1209_; lean_object* v_expandedMacroDecls_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_a_1206_);
v_a_1207_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1205_);
v_macroScope_1208_ = lean_ctor_get(v_a_1206_, 0);
lean_inc(v_macroScope_1208_);
v_traceMsgs_1209_ = lean_ctor_get(v_a_1206_, 1);
lean_inc(v_traceMsgs_1209_);
v_expandedMacroDecls_1210_ = lean_ctor_get(v_a_1206_, 2);
lean_inc(v_expandedMacroDecls_1210_);
lean_dec(v_a_1206_);
v___x_1211_ = lean_box(0);
v___x_1212_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1210_, v___x_1211_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v_expandedMacroDecls_1210_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1213_; lean_object* v_env_1214_; lean_object* v_ngen_1215_; lean_object* v_auxDeclNGen_1216_; lean_object* v_traceState_1217_; lean_object* v_cache_1218_; lean_object* v_messages_1219_; lean_object* v_infoState_1220_; lean_object* v_snapshotTasks_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___x_1212_);
v___x_1213_ = lean_st_ref_take(v___y_1182_);
v_env_1214_ = lean_ctor_get(v___x_1213_, 0);
v_ngen_1215_ = lean_ctor_get(v___x_1213_, 2);
v_auxDeclNGen_1216_ = lean_ctor_get(v___x_1213_, 3);
v_traceState_1217_ = lean_ctor_get(v___x_1213_, 4);
v_cache_1218_ = lean_ctor_get(v___x_1213_, 5);
v_messages_1219_ = lean_ctor_get(v___x_1213_, 6);
v_infoState_1220_ = lean_ctor_get(v___x_1213_, 7);
v_snapshotTasks_1221_ = lean_ctor_get(v___x_1213_, 8);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1213_, 1);
lean_dec(v_unused_1248_);
v___x_1223_ = v___x_1213_;
v_isShared_1224_ = v_isSharedCheck_1247_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snapshotTasks_1221_);
lean_inc(v_infoState_1220_);
lean_inc(v_messages_1219_);
lean_inc(v_cache_1218_);
lean_inc(v_traceState_1217_);
lean_inc(v_auxDeclNGen_1216_);
lean_inc(v_ngen_1215_);
lean_inc(v_env_1214_);
lean_dec(v___x_1213_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1247_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v_macroScope_1208_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_env_1214_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_macroScope_1208_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_ngen_1215_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_auxDeclNGen_1216_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_traceState_1217_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v_cache_1218_);
lean_ctor_set(v_reuseFailAlloc_1246_, 6, v_messages_1219_);
lean_ctor_set(v_reuseFailAlloc_1246_, 7, v_infoState_1220_);
lean_ctor_set(v_reuseFailAlloc_1246_, 8, v_snapshotTasks_1221_);
v___x_1226_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_st_ref_set(v___y_1182_, v___x_1226_);
v___x_1228_ = l_List_reverse___redArg(v_traceMsgs_1209_);
v___x_1229_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1228_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1237_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_a_1207_);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1207_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_a_1207_);
v_a_1238_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1229_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1229_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_traceMsgs_1209_);
lean_dec(v_macroScope_1208_);
lean_dec(v_a_1207_);
v_a_1249_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1212_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1212_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; 
v_a_1257_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1205_);
if (lean_obj_tag(v_a_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_a_1258_ = lean_ctor_get(v_a_1257_, 0);
lean_inc(v_a_1258_);
v_a_1259_ = lean_ctor_get(v_a_1257_, 1);
lean_inc_ref(v_a_1259_);
lean_dec_ref(v_a_1257_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1261_ = lean_string_dec_eq(v_a_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1259_);
v___x_1263_ = l_Lean_MessageData_ofFormat(v___x_1262_);
v___x_1264_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1258_, v___x_1263_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v_a_1258_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
lean_dec_ref(v_a_1259_);
v___x_1265_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1258_);
return v___x_1265_;
}
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1279_, size_t v_i_1280_, lean_object* v_bs_1281_){
_start:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_usize_dec_lt(v_i_1280_, v_sz_1279_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_bs_1281_);
return v___x_1283_;
}
else
{
lean_object* v_v_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_v_1284_ = lean_array_uget(v_bs_1281_, v_i_1280_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1284_);
v___x_1286_ = l_Lean_Syntax_isOfKind(v_v_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_v_1284_);
lean_dec_ref(v_bs_1281_);
v___x_1287_ = lean_box(0);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = l_Lean_Syntax_getArg(v_v_1284_, v___x_1288_);
v___x_1290_ = l_Lean_Syntax_isOfKind(v___x_1289_, v___x_1285_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
lean_dec(v_v_1284_);
lean_dec_ref(v_bs_1281_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; lean_object* v_bs_x27_1293_; lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = lean_unsigned_to_nat(3u);
v_bs_x27_1293_ = lean_array_uset(v_bs_1281_, v_i_1280_, v___x_1288_);
v___x_1294_ = l_Lean_Syntax_getArg(v_v_1284_, v___x_1292_);
lean_dec(v_v_1284_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1280_, v___x_1295_);
v___x_1297_ = lean_array_uset(v_bs_x27_1293_, v_i_1280_, v___x_1294_);
v_i_1280_ = v___x_1296_;
v_bs_1281_ = v___x_1297_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_bs_1301_){
_start:
{
size_t v_sz_boxed_1302_; size_t v_i_boxed_1303_; lean_object* v_res_1304_; 
v_sz_boxed_1302_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1303_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1302_, v_i_boxed_1303_, v_bs_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1317_, size_t v_i_1318_, lean_object* v_bs_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_usize_dec_lt(v_i_1318_, v_sz_1317_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_bs_1319_);
return v___x_1321_;
}
else
{
lean_object* v_v_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_v_1322_ = lean_array_uget(v_bs_1319_, v_i_1318_);
v___x_1323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1322_);
v___x_1324_ = l_Lean_Syntax_isOfKind(v_v_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec(v_v_1322_);
lean_dec_ref(v_bs_1319_);
v___x_1325_ = lean_box(0);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = l_Lean_Syntax_getArg(v_v_1322_, v___x_1326_);
v___x_1328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1329_ = l_Lean_Syntax_isOfKind(v___x_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec(v_v_1322_);
lean_dec_ref(v_bs_1319_);
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_bs_x27_1333_; lean_object* v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1331_ = lean_unsigned_to_nat(3u);
v___x_1332_ = lean_unsigned_to_nat(0u);
v_bs_x27_1333_ = lean_array_uset(v_bs_1319_, v_i_1318_, v___x_1332_);
v___x_1334_ = l_Lean_Syntax_getArg(v_v_1322_, v___x_1331_);
lean_dec(v_v_1322_);
v___x_1335_ = ((size_t)1ULL);
v___x_1336_ = lean_usize_add(v_i_1318_, v___x_1335_);
v___x_1337_ = lean_array_uset(v_bs_x27_1333_, v_i_1318_, v___x_1334_);
v_i_1318_ = v___x_1336_;
v_bs_1319_ = v___x_1337_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1339_, lean_object* v_i_1340_, lean_object* v_bs_1341_){
_start:
{
size_t v_sz_boxed_1342_; size_t v_i_boxed_1343_; lean_object* v_res_1344_; 
v_sz_boxed_1342_ = lean_unbox_usize(v_sz_1339_);
lean_dec(v_sz_1339_);
v_i_boxed_1343_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_res_1344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1342_, v_i_boxed_1343_, v_bs_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_bs_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_bs_1353_);
return v___x_1355_;
}
else
{
lean_object* v_v_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_v_1356_ = lean_array_uget(v_bs_1353_, v_i_1352_);
v___x_1357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1356_);
v___x_1358_ = l_Lean_Syntax_isOfKind(v_v_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec(v_v_1356_);
lean_dec_ref(v_bs_1353_);
v___x_1359_ = lean_box(0);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v_bs_x27_1361_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v_bs_x27_1361_ = lean_array_uset(v_bs_1353_, v_i_1352_, v___x_1360_);
v___x_1368_ = l_Lean_Syntax_getArg(v_v_1356_, v___x_1360_);
lean_dec(v_v_1356_);
v___x_1369_ = l_Lean_Syntax_isNone(v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(2u);
v___x_1371_ = l_Lean_Syntax_matchesNull(v___x_1368_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_bs_x27_1361_);
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
else
{
goto v___jp_1362_;
}
}
else
{
lean_dec(v___x_1368_);
goto v___jp_1362_;
}
v___jp_1362_:
{
lean_object* v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_add(v_i_1352_, v___x_1364_);
v___x_1366_ = lean_array_uset(v_bs_x27_1361_, v_i_1352_, v___x_1363_);
v_i_1352_ = v___x_1365_;
v_bs_1353_ = v___x_1366_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1373_, lean_object* v_i_1374_, lean_object* v_bs_1375_){
_start:
{
size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1373_);
lean_dec(v_sz_1373_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1376_, v_i_boxed_1377_, v_bs_1375_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_bs_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_bs_1381_);
return v___x_1383_;
}
else
{
lean_object* v_v_1384_; lean_object* v___x_1385_; lean_object* v_bs_x27_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_v_1384_ = lean_array_uget(v_bs_1381_, v_i_1380_);
v___x_1385_ = lean_unsigned_to_nat(0u);
v_bs_x27_1386_ = lean_array_uset(v_bs_1381_, v_i_1380_, v___x_1385_);
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_add(v_i_1380_, v___x_1387_);
v___x_1389_ = lean_array_uset(v_bs_x27_1386_, v_i_1380_, v_v_1384_);
v_i_1380_ = v___x_1388_;
v_bs_1381_ = v___x_1389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_bs_1393_){
_start:
{
size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1394_, v_i_boxed_1395_, v_bs_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1398_, v___y_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_x_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1402_, v_x_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec_ref(v_x_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1410_, lean_object* v_as_x27_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
if (lean_obj_tag(v_as_x27_1411_) == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_stx_1410_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_b_1412_);
return v___x_1420_;
}
else
{
lean_object* v_head_1421_; lean_object* v_tail_1422_; lean_object* v_value_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec_ref(v_b_1412_);
v_head_1421_ = lean_ctor_get(v_as_x27_1411_, 0);
v_tail_1422_ = lean_ctor_get(v_as_x27_1411_, 1);
v_value_1423_ = lean_ctor_get(v_head_1421_, 1);
v___x_1424_ = lean_box(0);
lean_inc(v_value_1423_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
lean_inc(v_stx_1410_);
v___x_1425_ = lean_apply_8(v_value_1423_, v_stx_1410_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, lean_box(0));
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_stx_1410_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1426_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1424_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1431_);
v___x_1433_ = v___x_1428_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1458_; 
v_a_1436_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1438_ = v___x_1425_;
v_isShared_1439_ = v_isSharedCheck_1458_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1425_);
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
lean_dec(v_stx_1410_);
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
lean_dec(v_stx_1410_);
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
v_as_x27_1411_ = v_tail_1422_;
v_b_1412_ = v___x_1440_;
goto _start;
}
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_stx_1410_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1459_, lean_object* v_as_x27_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1459_, v_as_x27_1460_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_as_x27_1460_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1472_, lean_object* v_rhs_x3f_1473_, lean_object* v_otherwise_x3f_1474_, lean_object* v_body_x3f_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
uint8_t v___y_1484_; uint8_t v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v_body_1494_; lean_object* v___y_1514_; lean_object* v_otherwise_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v_rhs_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; 
if (lean_obj_tag(v_rhs_x3f_1473_) == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1527_ = v___x_1538_;
v___y_1528_ = v_a_1476_;
v___y_1529_ = v_a_1477_;
v___y_1530_ = v_a_1478_;
v___y_1531_ = v_a_1479_;
v___y_1532_ = v_a_1480_;
v___y_1533_ = v_a_1481_;
goto v___jp_1526_;
}
else
{
lean_object* v_val_1539_; lean_object* v___x_1540_; 
v_val_1539_ = lean_ctor_get(v_rhs_x3f_1473_, 0);
lean_inc(v_val_1539_);
lean_dec_ref(v_rhs_x3f_1473_);
v___x_1540_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1539_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v_rhs_1527_ = v_a_1541_;
v___y_1528_ = v_a_1476_;
v___y_1529_ = v_a_1477_;
v___y_1530_ = v_a_1478_;
v___y_1531_ = v_a_1479_;
v___y_1532_ = v_a_1480_;
v___y_1533_ = v_a_1481_;
goto v___jp_1526_;
}
else
{
lean_dec(v_body_x3f_1475_);
lean_dec(v_otherwise_x3f_1474_);
lean_dec_ref(v_reassigned_1472_);
return v___x_1540_;
}
}
v___jp_1483_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1489_, 0, v___y_1486_);
lean_ctor_set(v___x_1489_, 1, v___y_1488_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*2, v___y_1487_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*2 + 1, v___y_1485_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*2 + 2, v___y_1484_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
v___jp_1491_:
{
lean_object* v___x_1495_; lean_object* v_info_1496_; uint8_t v_breaks_1497_; uint8_t v_continues_1498_; uint8_t v_returnsEarly_1499_; lean_object* v_numRegularExits_1500_; lean_object* v_reassigns_1501_; size_t v_sz_1502_; size_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1495_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1494_, v___y_1492_);
v_info_1496_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1493_, v___x_1495_);
v_breaks_1497_ = lean_ctor_get_uint8(v_info_1496_, sizeof(void*)*2);
v_continues_1498_ = lean_ctor_get_uint8(v_info_1496_, sizeof(void*)*2 + 1);
v_returnsEarly_1499_ = lean_ctor_get_uint8(v_info_1496_, sizeof(void*)*2 + 2);
v_numRegularExits_1500_ = lean_ctor_get(v_info_1496_, 0);
lean_inc(v_numRegularExits_1500_);
v_reassigns_1501_ = lean_ctor_get(v_info_1496_, 1);
lean_inc(v_reassigns_1501_);
lean_dec_ref(v_info_1496_);
v_sz_1502_ = lean_array_size(v_reassigned_1472_);
v___x_1503_ = ((size_t)0ULL);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1502_, v___x_1503_, v_reassigned_1472_);
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = lean_array_get_size(v___x_1504_);
v___x_1507_ = lean_nat_dec_lt(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_dec_ref(v___x_1504_);
v___y_1484_ = v_returnsEarly_1499_;
v___y_1485_ = v_continues_1498_;
v___y_1486_ = v_numRegularExits_1500_;
v___y_1487_ = v_breaks_1497_;
v___y_1488_ = v_reassigns_1501_;
goto v___jp_1483_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_nat_dec_le(v___x_1506_, v___x_1506_);
if (v___x_1508_ == 0)
{
if (v___x_1507_ == 0)
{
lean_dec_ref(v___x_1504_);
v___y_1484_ = v_returnsEarly_1499_;
v___y_1485_ = v_continues_1498_;
v___y_1486_ = v_numRegularExits_1500_;
v___y_1487_ = v_breaks_1497_;
v___y_1488_ = v_reassigns_1501_;
goto v___jp_1483_;
}
else
{
size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_usize_of_nat(v___x_1506_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1504_, v___x_1503_, v___x_1509_, v_reassigns_1501_);
lean_dec_ref(v___x_1504_);
v___y_1484_ = v_returnsEarly_1499_;
v___y_1485_ = v_continues_1498_;
v___y_1486_ = v_numRegularExits_1500_;
v___y_1487_ = v_breaks_1497_;
v___y_1488_ = v___x_1510_;
goto v___jp_1483_;
}
}
else
{
size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_usize_of_nat(v___x_1506_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1504_, v___x_1503_, v___x_1511_, v_reassigns_1501_);
lean_dec_ref(v___x_1504_);
v___y_1484_ = v_returnsEarly_1499_;
v___y_1485_ = v_continues_1498_;
v___y_1486_ = v_numRegularExits_1500_;
v___y_1487_ = v_breaks_1497_;
v___y_1488_ = v___x_1512_;
goto v___jp_1483_;
}
}
}
v___jp_1513_:
{
if (lean_obj_tag(v_body_x3f_1475_) == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1492_ = v_otherwise_1515_;
v___y_1493_ = v___y_1514_;
v_body_1494_ = v___x_1522_;
goto v___jp_1491_;
}
else
{
lean_object* v_val_1523_; lean_object* v___x_1524_; 
v_val_1523_ = lean_ctor_get(v_body_x3f_1475_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v_body_x3f_1475_);
v___x_1524_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1523_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___y_1492_ = v_otherwise_1515_;
v___y_1493_ = v___y_1514_;
v_body_1494_ = v_a_1525_;
goto v___jp_1491_;
}
else
{
lean_dec_ref(v_otherwise_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_reassigned_1472_);
return v___x_1524_;
}
}
}
v___jp_1526_:
{
if (lean_obj_tag(v_otherwise_x3f_1474_) == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1514_ = v_rhs_1527_;
v_otherwise_1515_ = v___x_1534_;
v___y_1516_ = v___y_1528_;
v___y_1517_ = v___y_1529_;
v___y_1518_ = v___y_1530_;
v___y_1519_ = v___y_1531_;
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1535_; lean_object* v___x_1536_; 
v_val_1535_ = lean_ctor_get(v_otherwise_x3f_1474_, 0);
lean_inc(v_val_1535_);
lean_dec_ref(v_otherwise_x3f_1474_);
v___x_1536_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1535_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
v___y_1514_ = v_rhs_1527_;
v_otherwise_1515_ = v_a_1537_;
v___y_1516_ = v___y_1528_;
v___y_1517_ = v___y_1529_;
v___y_1518_ = v___y_1530_;
v___y_1519_ = v___y_1531_;
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
goto v___jp_1513_;
}
else
{
lean_dec_ref(v_rhs_1527_);
lean_dec(v_body_x3f_1475_);
lean_dec_ref(v_reassigned_1472_);
return v___x_1536_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1556_ = l_Lean_stringToMessageData(v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1644_, lean_object* v_decl_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v_reassigns_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1645_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v_decl_1645_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1645_);
v___x_1684_ = l_Lean_Syntax_isOfKind(v_decl_1645_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1685_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1686_ = lean_box(0);
v___x_1687_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1686_, v___x_1684_);
v___x_1688_ = l_Std_Format_defWidth;
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = l_Std_Format_pretty(v___x_1687_, v___x_1688_, v___x_1689_, v___x_1689_);
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1685_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1692_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v_pattern_1695_; lean_object* v___y_1697_; lean_object* v_otherwise_x3f_1698_; lean_object* v_body_x3f_x3f_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v_body_x3f_x3f_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___x_1729_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1694_ = lean_unsigned_to_nat(0u);
v_pattern_1695_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1694_);
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1768_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1729_);
v___x_1769_ = l_Lean_Syntax_isNone(v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
lean_inc(v___x_1768_);
v___x_1770_ = l_Lean_Syntax_matchesNull(v___x_1768_, v___x_1729_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec(v___x_1768_);
lean_dec(v_pattern_1695_);
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1772_, v___x_1770_);
v___x_1774_ = l_Std_Format_defWidth;
v___x_1775_ = l_Std_Format_pretty(v___x_1773_, v___x_1774_, v___x_1694_, v___x_1694_);
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1771_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1777_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = l_Lean_Syntax_getArg(v___x_1768_, v___x_1694_);
lean_dec(v___x_1768_);
v___x_1780_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1781_ = l_Lean_Syntax_isOfKind(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v_pattern_1695_);
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1783_, v___x_1781_);
v___x_1785_ = l_Std_Format_defWidth;
v___x_1786_ = l_Std_Format_pretty(v___x_1784_, v___x_1785_, v___x_1694_, v___x_1694_);
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1782_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1788_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1789_;
}
else
{
v___y_1731_ = v_a_1646_;
v___y_1732_ = v_a_1647_;
v___y_1733_ = v_a_1648_;
v___y_1734_ = v_a_1649_;
v___y_1735_ = v_a_1650_;
v___y_1736_ = v_a_1651_;
goto v___jp_1730_;
}
}
}
else
{
lean_dec(v___x_1768_);
v___y_1731_ = v_a_1646_;
v___y_1732_ = v_a_1647_;
v___y_1733_ = v_a_1648_;
v___y_1734_ = v_a_1649_;
v___y_1735_ = v_a_1650_;
v___y_1736_ = v_a_1651_;
goto v___jp_1730_;
}
v___jp_1696_:
{
if (v_reassignment_1644_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_pattern_1695_);
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1666_ = v_otherwise_x3f_1698_;
v___y_1667_ = v___y_1697_;
v___y_1668_ = v_body_x3f_x3f_1699_;
v_reassigns_1669_ = v___x_1706_;
v___y_1670_ = v___y_1700_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___y_1703_;
v___y_1674_ = v___y_1704_;
v___y_1675_ = v___y_1705_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1695_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1707_);
v___y_1666_ = v_otherwise_x3f_1698_;
v___y_1667_ = v___y_1697_;
v___y_1668_ = v_body_x3f_x3f_1699_;
v_reassigns_1669_ = v_a_1708_;
v___y_1670_ = v___y_1700_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___y_1703_;
v___y_1674_ = v___y_1704_;
v___y_1675_ = v___y_1705_;
goto v___jp_1665_;
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_body_x3f_x3f_1699_);
lean_dec(v_otherwise_x3f_1698_);
lean_dec(v___y_1697_);
v_a_1709_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1707_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1707_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
v___jp_1717_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___y_1719_);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_body_x3f_x3f_1720_);
v___y_1697_ = v___y_1718_;
v_otherwise_x3f_1698_ = v___x_1727_;
v_body_x3f_x3f_1699_ = v___x_1728_;
v___y_1700_ = v___y_1721_;
v___y_1701_ = v___y_1722_;
v___y_1702_ = v___y_1723_;
v___y_1703_ = v___y_1724_;
v___y_1704_ = v___y_1725_;
v___y_1705_ = v___y_1726_;
goto v___jp_1696_;
}
v___jp_1730_:
{
lean_object* v___x_1737_; lean_object* v_rhs_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1737_ = lean_unsigned_to_nat(3u);
v_rhs_1738_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1737_);
v___x_1739_ = lean_unsigned_to_nat(4u);
v___x_1740_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1739_);
v___x_1741_ = l_Lean_Syntax_isNone(v___x_1740_);
if (v___x_1741_ == 0)
{
uint8_t v___x_1742_; 
lean_inc(v___x_1740_);
v___x_1742_ = l_Lean_Syntax_matchesNull(v___x_1740_, v___x_1737_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v___x_1740_);
lean_dec(v_rhs_1738_);
lean_dec(v_pattern_1695_);
v___x_1743_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1744_ = lean_box(0);
v___x_1745_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1744_, v___x_1742_);
v___x_1746_ = l_Std_Format_defWidth;
v___x_1747_ = l_Std_Format_pretty(v___x_1745_, v___x_1746_, v___x_1694_, v___x_1694_);
v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1743_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1749_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v_otherwise_x3f_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1751_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1752_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1729_);
v___x_1753_ = l_Lean_Syntax_getArg(v___x_1740_, v___x_1751_);
lean_dec(v___x_1740_);
v___x_1754_ = l_Lean_Syntax_isNone(v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
lean_inc(v___x_1753_);
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1753_, v___x_1729_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v___x_1753_);
lean_dec(v_otherwise_x3f_1752_);
lean_dec(v_rhs_1738_);
lean_dec(v_pattern_1695_);
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1757_ = lean_box(0);
v___x_1758_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1757_, v___x_1755_);
v___x_1759_ = l_Std_Format_defWidth;
v___x_1760_ = l_Std_Format_pretty(v___x_1758_, v___x_1759_, v___x_1694_, v___x_1694_);
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1756_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1762_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1763_;
}
else
{
lean_object* v_body_x3f_x3f_1764_; lean_object* v___x_1765_; 
lean_dec(v_decl_1645_);
v_body_x3f_x3f_1764_ = l_Lean_Syntax_getArg(v___x_1753_, v___x_1694_);
lean_dec(v___x_1753_);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_body_x3f_x3f_1764_);
v___y_1718_ = v_rhs_1738_;
v___y_1719_ = v_otherwise_x3f_1752_;
v_body_x3f_x3f_1720_ = v___x_1765_;
v___y_1721_ = v___y_1731_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___y_1734_;
v___y_1725_ = v___y_1735_;
v___y_1726_ = v___y_1736_;
goto v___jp_1717_;
}
}
else
{
lean_object* v___x_1766_; 
lean_dec(v___x_1753_);
lean_dec(v_decl_1645_);
v___x_1766_ = lean_box(0);
v___y_1718_ = v_rhs_1738_;
v___y_1719_ = v_otherwise_x3f_1752_;
v_body_x3f_x3f_1720_ = v___x_1766_;
v___y_1721_ = v___y_1731_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___y_1734_;
v___y_1725_ = v___y_1735_;
v___y_1726_ = v___y_1736_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v___x_1767_; 
lean_dec(v___x_1740_);
lean_dec(v_decl_1645_);
v___x_1767_ = lean_box(0);
v___y_1697_ = v_rhs_1738_;
v_otherwise_x3f_1698_ = v___x_1767_;
v_body_x3f_x3f_1699_ = v___x_1767_;
v___y_1700_ = v___y_1731_;
v___y_1701_ = v___y_1732_;
v___y_1702_ = v___y_1733_;
v___y_1703_ = v___y_1734_;
v___y_1704_ = v___y_1735_;
v___y_1705_ = v___y_1736_;
goto v___jp_1696_;
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v_x_1791_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v_x_1791_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1790_);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1791_);
v___x_1806_ = l_Lean_Syntax_isOfKind(v_x_1791_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v_x_1791_);
v___x_1807_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1808_ = lean_box(0);
v___x_1809_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1808_, v___x_1806_);
v___x_1810_ = l_Std_Format_defWidth;
v___x_1811_ = l_Std_Format_pretty(v___x_1809_, v___x_1810_, v___x_1790_, v___x_1790_);
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1813_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1815_);
v___x_1817_ = l_Lean_Syntax_isNone(v___x_1816_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; 
lean_inc(v___x_1816_);
v___x_1818_ = l_Lean_Syntax_matchesNull(v___x_1816_, v___x_1815_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec(v___x_1816_);
lean_dec(v_x_1791_);
v___x_1819_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1820_ = lean_box(0);
v___x_1821_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1820_, v___x_1818_);
v___x_1822_ = l_Std_Format_defWidth;
v___x_1823_ = l_Std_Format_pretty(v___x_1821_, v___x_1822_, v___x_1790_, v___x_1790_);
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1819_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1825_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = l_Lean_Syntax_getArg(v___x_1816_, v___x_1790_);
lean_dec(v___x_1816_);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1829_ = l_Lean_Syntax_isOfKind(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v_x_1791_);
v___x_1830_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1831_ = lean_box(0);
v___x_1832_ = l_Lean_Syntax_formatStx(v_decl_1645_, v___x_1831_, v___x_1829_);
v___x_1833_ = l_Std_Format_defWidth;
v___x_1834_ = l_Std_Format_pretty(v___x_1832_, v___x_1833_, v___x_1790_, v___x_1790_);
v___x_1835_ = l_Lean_stringToMessageData(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1830_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1836_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
return v___x_1837_;
}
else
{
v___y_1793_ = v_a_1646_;
v___y_1794_ = v_a_1647_;
v___y_1795_ = v_a_1648_;
v___y_1796_ = v_a_1649_;
v___y_1797_ = v_a_1650_;
v___y_1798_ = v_a_1651_;
goto v___jp_1792_;
}
}
}
else
{
lean_dec(v___x_1816_);
v___y_1793_ = v_a_1646_;
v___y_1794_ = v_a_1647_;
v___y_1795_ = v_a_1648_;
v___y_1796_ = v_a_1649_;
v___y_1797_ = v_a_1650_;
v___y_1798_ = v_a_1651_;
goto v___jp_1792_;
}
}
v___jp_1792_:
{
lean_object* v___x_1799_; lean_object* v_rhs_1800_; 
v___x_1799_ = lean_unsigned_to_nat(3u);
v_rhs_1800_ = l_Lean_Syntax_getArg(v_decl_1645_, v___x_1799_);
lean_dec(v_decl_1645_);
if (v_reassignment_1644_ == 0)
{
lean_object* v___x_1801_; 
lean_dec(v_x_1791_);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1654_ = v___y_1798_;
v___y_1655_ = v___y_1795_;
v___y_1656_ = v___y_1796_;
v___y_1657_ = v___y_1793_;
v___y_1658_ = v_rhs_1800_;
v___y_1659_ = v___y_1797_;
v___y_1660_ = v___y_1794_;
v___y_1661_ = v___x_1801_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_mk_empty_array_with_capacity(v___x_1802_);
v___x_1804_ = lean_array_push(v___x_1803_, v_x_1791_);
v___y_1654_ = v___y_1798_;
v___y_1655_ = v___y_1795_;
v___y_1656_ = v___y_1796_;
v___y_1657_ = v___y_1793_;
v___y_1658_ = v_rhs_1800_;
v___y_1659_ = v___y_1797_;
v___y_1660_ = v___y_1794_;
v___y_1661_ = v___x_1804_;
goto v___jp_1653_;
}
}
}
v___jp_1653_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___y_1658_);
v___x_1663_ = lean_box(0);
v___x_1664_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1661_, v___x_1662_, v___x_1663_, v___x_1663_, v___y_1657_, v___y_1660_, v___y_1655_, v___y_1656_, v___y_1659_, v___y_1654_);
return v___x_1664_;
}
v___jp_1665_:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___y_1667_);
if (lean_obj_tag(v___y_1668_) == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_box(0);
v___x_1678_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1669_, v___x_1676_, v___y_1666_, v___x_1677_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
return v___x_1678_;
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1680_; 
v_val_1679_ = lean_ctor_get(v___y_1668_, 0);
lean_inc(v_val_1679_);
lean_dec_ref(v___y_1668_);
v___x_1680_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1669_, v___x_1676_, v___y_1666_, v_val_1679_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1954_, size_t v_sz_1955_, size_t v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_lt(v_i_1956_, v_sz_1955_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_b_1957_);
return v___x_1966_;
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_array_uget_borrowed(v_as_1954_, v_i_1956_);
lean_inc(v_a_1967_);
v___x_1968_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1967_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1969_, v_b_1957_);
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1956_, v___x_1971_);
v_i_1956_ = v___x_1972_;
v_b_1957_ = v___x_1970_;
goto _start;
}
else
{
lean_dec_ref(v_b_1957_);
return v___x_1968_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2003_, lean_object* v_as_2004_, size_t v_sz_2005_, size_t v_i_2006_, lean_object* v_b_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_a_2016_; uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2006_, v_sz_2005_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_b_2007_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; lean_object* v_a_2023_; uint8_t v___x_2024_; 
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2023_ = lean_array_uget_borrowed(v_as_2004_, v_i_2006_);
lean_inc(v_a_2023_);
v___x_2024_ = l_Lean_Syntax_isOfKind(v_a_2023_, v___x_2022_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_dec_ref(v___x_2025_);
v_a_2016_ = v_b_2007_;
goto v___jp_2015_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_b_2007_);
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
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
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___y_2037_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_unsigned_to_nat(3u);
v___x_2054_ = l_Lean_Syntax_getArg(v_a_2023_, v___x_2034_);
v___x_2055_ = l_Lean_Syntax_getArgs(v___x_2054_);
lean_dec(v___x_2054_);
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2058_ = lean_array_get_size(v___x_2055_);
v___x_2059_ = lean_nat_dec_lt(v___x_2056_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_dec_ref(v___x_2055_);
v___y_2037_ = v___x_2057_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2060_ = lean_box(v___x_2024_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2057_);
v___x_2062_ = lean_nat_dec_le(v___x_2058_, v___x_2058_);
if (v___x_2062_ == 0)
{
if (v___x_2059_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v___x_2055_);
v___y_2037_ = v___x_2057_;
goto v___jp_2036_;
}
else
{
size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; lean_object* v_snd_2066_; 
v___x_2063_ = ((size_t)0ULL);
v___x_2064_ = lean_usize_of_nat(v___x_2058_);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2024_, v___x_2003_, v___x_2055_, v___x_2063_, v___x_2064_, v___x_2061_);
lean_dec_ref(v___x_2055_);
v_snd_2066_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_snd_2066_);
lean_dec_ref(v___x_2065_);
v___y_2037_ = v_snd_2066_;
goto v___jp_2036_;
}
}
else
{
size_t v___x_2067_; size_t v___x_2068_; lean_object* v___x_2069_; lean_object* v_snd_2070_; 
v___x_2067_ = ((size_t)0ULL);
v___x_2068_ = lean_usize_of_nat(v___x_2058_);
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2024_, v___x_2003_, v___x_2055_, v___x_2067_, v___x_2068_, v___x_2061_);
lean_dec_ref(v___x_2055_);
v_snd_2070_ = lean_ctor_get(v___x_2069_, 1);
lean_inc(v_snd_2070_);
lean_dec_ref(v___x_2069_);
v___y_2037_ = v_snd_2070_;
goto v___jp_2036_;
}
}
v___jp_2036_:
{
size_t v_sz_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v_sz_2038_ = lean_array_size(v___y_2037_);
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2038_, v___x_2039_, v___y_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref(v___x_2041_);
v_a_2016_ = v_b_2007_;
goto v___jp_2015_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_b_2007_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec_ref(v___x_2040_);
v___x_2050_ = l_Lean_Syntax_getArg(v_a_2023_, v___x_2035_);
v___x_2051_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2050_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2007_, v_a_2052_);
v_a_2016_ = v___x_2053_;
goto v___jp_2015_;
}
else
{
lean_dec_ref(v_b_2007_);
return v___x_2051_;
}
}
}
}
}
v___jp_2015_:
{
size_t v___x_2017_; size_t v___x_2018_; 
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2006_, v___x_2017_);
v_i_2006_ = v___x_2018_;
v_b_2007_ = v_a_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2071_, size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_a_2083_; uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_lt(v_i_2073_, v_sz_2072_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_b_2074_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v_a_2090_ = lean_array_uget_borrowed(v_as_2071_, v_i_2073_);
v___x_2103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2090_);
v___x_2104_ = l_Lean_Syntax_isOfKind(v_a_2090_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2090_);
v___x_2106_ = l_Lean_Syntax_isOfKind(v_a_2090_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2108_ = lean_box(0);
lean_inc(v_a_2090_);
v___x_2109_ = l_Lean_Syntax_formatStx(v_a_2090_, v___x_2108_, v___x_2106_);
v___x_2110_ = l_Std_Format_defWidth;
v___x_2111_ = l_Std_Format_pretty(v___x_2109_, v___x_2110_, v___x_2089_, v___x_2089_);
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2107_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2113_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_dec_ref(v___x_2114_);
v_a_2083_ = v_b_2074_;
goto v___jp_2082_;
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_b_2074_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = l_Lean_Syntax_getArg(v_a_2090_, v___x_2123_);
v___x_2125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2124_);
v___x_2126_ = l_Lean_Syntax_isOfKind(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec(v___x_2124_);
v___x_2127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2128_ = lean_box(0);
lean_inc(v_a_2090_);
v___x_2129_ = l_Lean_Syntax_formatStx(v_a_2090_, v___x_2128_, v___x_2126_);
v___x_2130_ = l_Std_Format_defWidth;
v___x_2131_ = l_Std_Format_pretty(v___x_2129_, v___x_2130_, v___x_2089_, v___x_2089_);
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2127_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2133_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_dec_ref(v___x_2134_);
v_a_2083_ = v_b_2074_;
goto v___jp_2082_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_b_2074_);
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; size_t v_sz_2145_; size_t v___x_2146_; lean_object* v___x_2147_; 
v___x_2143_ = l_Lean_Syntax_getArg(v___x_2124_, v___x_2089_);
lean_dec(v___x_2124_);
v___x_2144_ = l_Lean_Syntax_getArgs(v___x_2143_);
lean_dec(v___x_2143_);
v_sz_2145_ = lean_array_size(v___x_2144_);
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2104_, v___x_2144_, v_sz_2145_, v___x_2146_, v_b_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec_ref(v___x_2144_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v_a_2083_ = v_a_2148_;
goto v___jp_2082_;
}
else
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = lean_unsigned_to_nat(2u);
v___x_2150_ = l_Lean_Syntax_getArg(v_a_2090_, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_isNone(v___x_2150_);
if (v___x_2151_ == 0)
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_Syntax_matchesNull(v___x_2150_, v___x_2149_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2153_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2154_ = lean_box(0);
lean_inc(v_a_2090_);
v___x_2155_ = l_Lean_Syntax_formatStx(v_a_2090_, v___x_2154_, v___x_2152_);
v___x_2156_ = l_Std_Format_defWidth;
v___x_2157_ = l_Std_Format_pretty(v___x_2155_, v___x_2156_, v___x_2089_, v___x_2089_);
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2153_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2159_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_dec_ref(v___x_2160_);
v_a_2083_ = v_b_2074_;
goto v___jp_2082_;
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v_b_2074_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
v___y_2092_ = v___y_2075_;
v___y_2093_ = v___y_2076_;
v___y_2094_ = v___y_2077_;
v___y_2095_ = v___y_2078_;
v___y_2096_ = v___y_2079_;
v___y_2097_ = v___y_2080_;
goto v___jp_2091_;
}
}
else
{
lean_dec(v___x_2150_);
v___y_2092_ = v___y_2075_;
v___y_2093_ = v___y_2076_;
v___y_2094_ = v___y_2077_;
v___y_2095_ = v___y_2078_;
v___y_2096_ = v___y_2079_;
v___y_2097_ = v___y_2080_;
goto v___jp_2091_;
}
}
v___jp_2091_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_unsigned_to_nat(4u);
v___x_2099_ = l_Lean_Syntax_getArg(v_a_2090_, v___x_2098_);
v___x_2100_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2099_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2101_, v_b_2074_);
v_a_2083_ = v___x_2102_;
goto v___jp_2082_;
}
else
{
lean_dec_ref(v_b_2074_);
return v___x_2100_;
}
}
}
v___jp_2082_:
{
size_t v___x_2084_; size_t v___x_2085_; 
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_add(v_i_2073_, v___x_2084_);
v_i_2073_ = v___x_2085_;
v_b_2074_ = v_a_2083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2169_) == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
return v___x_2178_;
}
else
{
lean_object* v_val_2179_; lean_object* v___x_2180_; 
v_val_2179_ = lean_ctor_get(v_stx_x3f_2169_, 0);
lean_inc(v_val_2179_);
lean_dec_ref(v_stx_x3f_2169_);
v___x_2180_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2179_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2187_, lean_object* v_as_2188_, size_t v_sz_2189_, size_t v_i_2190_, lean_object* v_b_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_a_2200_; uint8_t v___x_2204_; 
v___x_2204_ = lean_usize_dec_lt(v_i_2190_, v_sz_2189_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_b_2191_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v_a_2207_; uint8_t v___x_2208_; 
v___x_2206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2207_ = lean_array_uget_borrowed(v_as_2188_, v_i_2190_);
lean_inc(v_a_2207_);
v___x_2208_ = l_Lean_Syntax_isOfKind(v_a_2207_, v___x_2206_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_dec_ref(v___x_2209_);
v_a_2200_ = v_b_2191_;
goto v___jp_2199_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_b_2191_);
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___y_2221_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_unsigned_to_nat(3u);
v___x_2238_ = l_Lean_Syntax_getArg(v_a_2207_, v___x_2218_);
v___x_2239_ = l_Lean_Syntax_getArgs(v___x_2238_);
lean_dec(v___x_2238_);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2242_ = lean_array_get_size(v___x_2239_);
v___x_2243_ = lean_nat_dec_lt(v___x_2240_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_dec_ref(v___x_2239_);
v___y_2221_ = v___x_2241_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2244_ = lean_box(v___x_2208_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2241_);
v___x_2246_ = lean_nat_dec_le(v___x_2242_, v___x_2242_);
if (v___x_2246_ == 0)
{
if (v___x_2243_ == 0)
{
lean_dec_ref(v___x_2245_);
lean_dec_ref(v___x_2239_);
v___y_2221_ = v___x_2241_;
goto v___jp_2220_;
}
else
{
size_t v___x_2247_; size_t v___x_2248_; lean_object* v___x_2249_; lean_object* v_snd_2250_; 
v___x_2247_ = ((size_t)0ULL);
v___x_2248_ = lean_usize_of_nat(v___x_2242_);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2208_, v___x_2187_, v___x_2239_, v___x_2247_, v___x_2248_, v___x_2245_);
lean_dec_ref(v___x_2239_);
v_snd_2250_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_snd_2250_);
lean_dec_ref(v___x_2249_);
v___y_2221_ = v_snd_2250_;
goto v___jp_2220_;
}
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; lean_object* v_snd_2254_; 
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = lean_usize_of_nat(v___x_2242_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2208_, v___x_2187_, v___x_2239_, v___x_2251_, v___x_2252_, v___x_2245_);
lean_dec_ref(v___x_2239_);
v_snd_2254_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2254_);
lean_dec_ref(v___x_2253_);
v___y_2221_ = v_snd_2254_;
goto v___jp_2220_;
}
}
v___jp_2220_:
{
size_t v_sz_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v_sz_2222_ = lean_array_size(v___y_2221_);
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2222_, v___x_2223_, v___y_2221_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_dec_ref(v___x_2225_);
v_a_2200_ = v_b_2191_;
goto v___jp_2199_;
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_b_2191_);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v___x_2224_);
v___x_2234_ = l_Lean_Syntax_getArg(v_a_2207_, v___x_2219_);
v___x_2235_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2234_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2191_, v_a_2236_);
v_a_2200_ = v___x_2237_;
goto v___jp_2199_;
}
else
{
lean_dec_ref(v_b_2191_);
return v___x_2235_;
}
}
}
}
}
v___jp_2199_:
{
size_t v___x_2201_; size_t v___x_2202_; 
v___x_2201_ = ((size_t)1ULL);
v___x_2202_ = lean_usize_add(v_i_2190_, v___x_2201_);
v_i_2190_ = v___x_2202_;
v_b_2191_ = v_a_2200_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2291_ = l_Lean_NameSet_empty;
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = 0;
v___x_2294_ = 1;
v___x_2295_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2295_, 0, v___x_2292_);
lean_ctor_set(v___x_2295_, 1, v___x_2291_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*2, v___x_2294_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*2 + 1, v___x_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*2 + 2, v___x_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2318_; lean_object* v_bodyInfo_2319_; lean_object* v___y_2323_; lean_object* v_bodyInfo_2324_; lean_object* v___x_2327_; lean_object* v_env_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2327_ = lean_st_ref_get(v_a_2302_);
v_env_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_ref(v_env_2328_);
lean_dec(v___x_2327_);
lean_inc(v_stx_2296_);
v___x_2329_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2329_, 0, v_env_2328_);
lean_closure_set(v___x_2329_, 1, v_stx_2296_);
v___x_2330_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2329_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_4387_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_4387_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_4387_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
if (lean_obj_tag(v_a_2331_) == 1)
{
lean_object* v_val_2335_; lean_object* v_snd_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_del_object(v___x_2333_);
lean_dec(v_stx_2296_);
v_val_2335_ = lean_ctor_get(v_a_2331_, 0);
lean_inc(v_val_2335_);
lean_dec_ref(v_a_2331_);
v_snd_2336_ = lean_ctor_get(v_val_2335_, 1);
lean_inc(v_snd_2336_);
lean_dec(v_val_2335_);
v___x_2337_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2337_, 0, lean_box(0));
lean_closure_set(v___x_2337_, 1, v_snd_2336_);
v___x_2338_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2337_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v_stx_2296_ = v_a_2339_;
goto _start;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2338_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2338_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___x_2531_; uint8_t v___x_2532_; uint8_t v___x_2533_; 
lean_dec(v_a_2331_);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2296_);
v___x_2532_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2531_);
v___x_2533_ = 1;
if (v___x_2532_ == 0)
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2296_);
v___x_2535_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2296_);
v___x_2537_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2296_);
v___x_2539_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2296_);
v___x_2541_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2296_);
v___x_2543_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; uint8_t v___x_2545_; 
lean_del_object(v___x_2333_);
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2296_);
v___x_2545_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2296_);
v___x_2547_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; 
v___x_2548_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2296_);
v___x_2549_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2296_);
v___x_2611_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2296_);
v___x_2613_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2296_);
v___x_2615_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2296_);
v___x_2617_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2296_);
v___x_2619_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2296_);
v___x_2621_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2296_);
v___x_2623_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2296_);
v___x_2625_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2296_);
v___x_2627_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50));
lean_inc(v_stx_2296_);
v___x_2629_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2296_);
v___x_2631_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2296_);
v___x_2633_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2296_);
v___x_2635_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2296_);
v___x_2637_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2296_);
v___x_2639_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2296_);
v___x_2641_ = l_Lean_Syntax_isOfKind(v_stx_2296_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v_env_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2642_ = lean_st_ref_get(v_a_2302_);
v_env_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc_ref(v_env_2643_);
lean_dec(v___x_2642_);
lean_inc_n(v_stx_2296_, 2);
v___x_2644_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2645_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2646_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2645_, v_env_2643_, v___x_2644_);
v___x_2647_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2648_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2646_, v___x_2647_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_2646_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2679_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2679_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2679_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2677_; 
v_fst_2653_ = lean_ctor_get(v_a_2649_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_a_2649_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_a_2649_, 1);
lean_dec(v_unused_2678_);
v___x_2655_ = v_a_2649_;
v_isShared_2656_ = v_isSharedCheck_2677_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_fst_2653_);
lean_dec(v_a_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2677_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
if (lean_obj_tag(v_fst_2653_) == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
lean_del_object(v___x_2651_);
v___x_2657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2658_ = l_Lean_MessageData_ofName(v___x_2644_);
lean_inc_ref(v___x_2658_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 7);
lean_ctor_set(v___x_2655_, 1, v___x_2658_);
lean_ctor_set(v___x_2655_, 0, v___x_2657_);
v___x_2660_ = v___x_2655_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2661_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2664_ = l_Lean_indentD(v___x_2663_);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2662_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v___x_2658_);
v___x_2669_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2670_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2671_;
}
}
else
{
lean_object* v_val_2673_; lean_object* v___x_2675_; 
lean_del_object(v___x_2655_);
lean_dec(v___x_2644_);
lean_dec(v_stx_2296_);
v_val_2673_ = lean_ctor_get(v_fst_2653_, 0);
lean_inc(v_val_2673_);
lean_dec_ref(v_fst_2653_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v_val_2673_);
v___x_2675_ = v___x_2651_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_val_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v___x_2644_);
lean_dec(v_stx_2296_);
v_a_2680_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2648_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2648_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___y_2692_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_unsigned_to_nat(5u);
v___x_2690_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2689_);
v___x_2701_ = lean_unsigned_to_nat(6u);
v___x_2702_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2701_);
lean_dec(v_stx_2296_);
v___x_2703_ = l_Lean_Syntax_getOptional_x3f(v___x_2702_);
lean_dec(v___x_2702_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_box(0);
v___y_2692_ = v___x_2704_;
goto v___jp_2691_;
}
else
{
lean_object* v_val_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
v_val_2705_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2703_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_val_2705_);
lean_dec(v___x_2703_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_val_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
v___y_2692_ = v___x_2710_;
goto v___jp_2691_;
}
}
}
v___jp_2691_:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2690_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2693_) == 0)
{
if (lean_obj_tag(v___y_2692_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = l_Lean_NameSet_empty;
v___x_2696_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2696_, 0, v___x_2688_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
lean_ctor_set_uint8(v___x_2696_, sizeof(void*)*2, v___x_2639_);
lean_ctor_set_uint8(v___x_2696_, sizeof(void*)*2 + 1, v___x_2639_);
lean_ctor_set_uint8(v___x_2696_, sizeof(void*)*2 + 2, v___x_2639_);
v___y_2318_ = v_a_2694_;
v_bodyInfo_2319_ = v___x_2696_;
goto v___jp_2317_;
}
else
{
lean_object* v_a_2697_; lean_object* v_val_2698_; lean_object* v___x_2699_; 
v_a_2697_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2693_);
v_val_2698_ = lean_ctor_get(v___y_2692_, 0);
lean_inc(v_val_2698_);
lean_dec_ref(v___y_2692_);
v___x_2699_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2698_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___y_2318_ = v_a_2697_;
v_bodyInfo_2319_ = v_a_2700_;
goto v___jp_2317_;
}
else
{
lean_dec(v_a_2697_);
return v___x_2699_;
}
}
}
else
{
lean_dec(v___y_2692_);
return v___x_2693_;
}
}
}
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___y_2717_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2713_ = lean_unsigned_to_nat(1u);
v___x_2714_ = lean_unsigned_to_nat(5u);
v___x_2715_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2714_);
v___x_2726_ = lean_unsigned_to_nat(6u);
v___x_2727_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2726_);
lean_dec(v_stx_2296_);
v___x_2728_ = l_Lean_Syntax_getOptional_x3f(v___x_2727_);
lean_dec(v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = lean_box(0);
v___y_2717_ = v___x_2729_;
goto v___jp_2716_;
}
else
{
lean_object* v_val_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
v_val_2730_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2728_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_val_2730_);
lean_dec(v___x_2728_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_val_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
v___y_2717_ = v___x_2735_;
goto v___jp_2716_;
}
}
}
v___jp_2716_:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2715_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2718_) == 0)
{
if (lean_obj_tag(v___y_2717_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref(v___x_2718_);
v___x_2720_ = l_Lean_NameSet_empty;
v___x_2721_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2721_, 0, v___x_2713_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*2, v___x_2637_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*2 + 1, v___x_2637_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*2 + 2, v___x_2637_);
v___y_2323_ = v_a_2719_;
v_bodyInfo_2324_ = v___x_2721_;
goto v___jp_2322_;
}
else
{
lean_object* v_a_2722_; lean_object* v_val_2723_; lean_object* v___x_2724_; 
v_a_2722_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2722_);
lean_dec_ref(v___x_2718_);
v_val_2723_ = lean_ctor_get(v___y_2717_, 0);
lean_inc(v_val_2723_);
lean_dec_ref(v___y_2717_);
v___x_2724_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2723_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref(v___x_2724_);
v___y_2323_ = v_a_2722_;
v_bodyInfo_2324_ = v_a_2725_;
goto v___jp_2322_;
}
else
{
lean_dec(v_a_2722_);
return v___x_2724_;
}
}
}
else
{
lean_dec(v___y_2717_);
return v___x_2718_;
}
}
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2953_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2739_);
v___x_2954_ = l_Lean_Syntax_isNone(v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = lean_unsigned_to_nat(5u);
v___x_2956_ = l_Lean_Syntax_matchesNull(v___x_2953_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v_env_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2957_ = lean_st_ref_get(v_a_2302_);
v_env_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc_ref(v_env_2958_);
lean_dec(v___x_2957_);
lean_inc_n(v_stx_2296_, 2);
v___x_2959_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2960_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2961_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2960_, v_env_2958_, v___x_2959_);
v___x_2962_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2963_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2961_, v___x_2962_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_2961_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2994_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2994_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2994_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_fst_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2992_; 
v_fst_2968_ = lean_ctor_get(v_a_2964_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_a_2964_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v_a_2964_, 1);
lean_dec(v_unused_2993_);
v___x_2970_ = v_a_2964_;
v_isShared_2971_ = v_isSharedCheck_2992_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_fst_2968_);
lean_dec(v_a_2964_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2992_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
if (lean_obj_tag(v_fst_2968_) == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_del_object(v___x_2966_);
v___x_2972_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2973_ = l_Lean_MessageData_ofName(v___x_2959_);
lean_inc_ref(v___x_2973_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 7);
lean_ctor_set(v___x_2970_, 1, v___x_2973_);
lean_ctor_set(v___x_2970_, 0, v___x_2972_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2976_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2979_ = l_Lean_indentD(v___x_2978_);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2977_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v___x_2973_);
v___x_2984_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2985_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2986_;
}
}
else
{
lean_object* v_val_2988_; lean_object* v___x_2990_; 
lean_del_object(v___x_2970_);
lean_dec(v___x_2959_);
lean_dec(v_stx_2296_);
v_val_2988_ = lean_ctor_get(v_fst_2968_, 0);
lean_inc(v_val_2988_);
lean_dec_ref(v_fst_2968_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v_val_2988_);
v___x_2990_ = v___x_2966_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_val_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___x_2959_);
lean_dec(v_stx_2296_);
v_a_2995_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2963_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2963_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
v___y_2741_ = v_a_2297_;
v___y_2742_ = v_a_2298_;
v___y_2743_ = v_a_2299_;
v___y_2744_ = v_a_2300_;
v___y_2745_ = v_a_2301_;
v___y_2746_ = v_a_2302_;
goto v___jp_2740_;
}
}
else
{
lean_dec(v___x_2953_);
v___y_2741_ = v_a_2297_;
v___y_2742_ = v_a_2298_;
v___y_2743_ = v_a_2299_;
v___y_2744_ = v_a_2300_;
v___y_2745_ = v_a_2301_;
v___y_2746_ = v_a_2302_;
goto v___jp_2740_;
}
v___jp_2740_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2747_ = lean_unsigned_to_nat(4u);
v___x_2748_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v___x_2748_);
v___x_2750_ = l_Lean_Syntax_isOfKind(v___x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v_env_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_dec(v___x_2748_);
v___x_2751_ = lean_st_ref_get(v___y_2746_);
v_env_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_env_2752_);
lean_dec(v___x_2751_);
lean_inc_n(v_stx_2296_, 2);
v___x_2753_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2754_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2755_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2754_, v_env_2752_, v___x_2753_);
v___x_2756_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2757_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2755_, v___x_2756_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___x_2755_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2788_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2788_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2788_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_fst_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2786_; 
v_fst_2762_ = lean_ctor_get(v_a_2758_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_a_2758_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v_a_2758_, 1);
lean_dec(v_unused_2787_);
v___x_2764_ = v_a_2758_;
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_fst_2762_);
lean_dec(v_a_2758_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
if (lean_obj_tag(v_fst_2762_) == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_del_object(v___x_2760_);
v___x_2766_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2767_ = l_Lean_MessageData_ofName(v___x_2753_);
lean_inc_ref(v___x_2767_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 7);
lean_ctor_set(v___x_2764_, 1, v___x_2767_);
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2769_ = v___x_2764_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2770_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2773_ = l_Lean_indentD(v___x_2772_);
v___x_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2771_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v___x_2767_);
v___x_2778_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2779_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2780_;
}
}
else
{
lean_object* v_val_2782_; lean_object* v___x_2784_; 
lean_del_object(v___x_2764_);
lean_dec(v___x_2753_);
lean_dec(v_stx_2296_);
v_val_2782_ = lean_ctor_get(v_fst_2762_, 0);
lean_inc(v_val_2782_);
lean_dec_ref(v_fst_2762_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_val_2782_);
v___x_2784_ = v___x_2760_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_val_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v___x_2753_);
lean_dec(v_stx_2296_);
v_a_2789_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2757_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2757_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; size_t v_sz_2799_; size_t v___x_2800_; lean_object* v___x_2801_; 
v___x_2797_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2738_);
v___x_2798_ = l_Lean_Syntax_getArgs(v___x_2797_);
lean_dec(v___x_2797_);
v_sz_2799_ = lean_array_size(v___x_2798_);
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2799_, v___x_2800_, v___x_2798_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v___x_2802_; lean_object* v_env_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_dec(v___x_2748_);
v___x_2802_ = lean_st_ref_get(v___y_2746_);
v_env_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2803_);
lean_dec(v___x_2802_);
lean_inc_n(v_stx_2296_, 2);
v___x_2804_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2805_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2806_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2805_, v_env_2803_, v___x_2804_);
v___x_2807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2808_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2806_, v___x_2807_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___x_2806_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2839_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2839_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2839_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_fst_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2837_; 
v_fst_2813_ = lean_ctor_get(v_a_2809_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_a_2809_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v_a_2809_, 1);
lean_dec(v_unused_2838_);
v___x_2815_ = v_a_2809_;
v_isShared_2816_ = v_isSharedCheck_2837_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_fst_2813_);
lean_dec(v_a_2809_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2837_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
if (lean_obj_tag(v_fst_2813_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
lean_del_object(v___x_2811_);
v___x_2817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2818_ = l_Lean_MessageData_ofName(v___x_2804_);
lean_inc_ref(v___x_2818_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 7);
lean_ctor_set(v___x_2815_, 1, v___x_2818_);
lean_ctor_set(v___x_2815_, 0, v___x_2817_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2821_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2824_ = l_Lean_indentD(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2822_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v___x_2818_);
v___x_2829_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2830_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2831_;
}
}
else
{
lean_object* v_val_2833_; lean_object* v___x_2835_; 
lean_del_object(v___x_2815_);
lean_dec(v___x_2804_);
lean_dec(v_stx_2296_);
v_val_2833_ = lean_ctor_get(v_fst_2813_, 0);
lean_inc(v_val_2833_);
lean_dec_ref(v_fst_2813_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v_val_2833_);
v___x_2835_ = v___x_2811_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_val_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___x_2804_);
lean_dec(v_stx_2296_);
v_a_2840_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2808_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2808_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_val_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_val_2848_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_val_2848_);
lean_dec_ref(v___x_2801_);
v___x_2849_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2739_);
lean_dec(v___x_2748_);
v___x_2850_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v___x_2849_);
v___x_2851_ = l_Lean_Syntax_isOfKind(v___x_2849_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v_env_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec(v___x_2849_);
lean_dec(v_val_2848_);
v___x_2852_ = lean_st_ref_get(v___y_2746_);
v_env_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_ref(v_env_2853_);
lean_dec(v___x_2852_);
lean_inc_n(v_stx_2296_, 2);
v___x_2854_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2855_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2856_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2855_, v_env_2853_, v___x_2854_);
v___x_2857_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2858_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2856_, v___x_2857_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___x_2856_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2889_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2889_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2889_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_fst_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2887_; 
v_fst_2863_ = lean_ctor_get(v_a_2859_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_a_2859_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v_a_2859_, 1);
lean_dec(v_unused_2888_);
v___x_2865_ = v_a_2859_;
v_isShared_2866_ = v_isSharedCheck_2887_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_fst_2863_);
lean_dec(v_a_2859_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2887_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
if (lean_obj_tag(v_fst_2863_) == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
lean_del_object(v___x_2861_);
v___x_2867_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2868_ = l_Lean_MessageData_ofName(v___x_2854_);
lean_inc_ref(v___x_2868_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set_tag(v___x_2865_, 7);
lean_ctor_set(v___x_2865_, 1, v___x_2868_);
lean_ctor_set(v___x_2865_, 0, v___x_2867_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2871_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2874_ = l_Lean_indentD(v___x_2873_);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2872_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v___x_2868_);
v___x_2879_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2880_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2881_;
}
}
else
{
lean_object* v_val_2883_; lean_object* v___x_2885_; 
lean_del_object(v___x_2865_);
lean_dec(v___x_2854_);
lean_dec(v_stx_2296_);
v_val_2883_ = lean_ctor_get(v_fst_2863_, 0);
lean_inc(v_val_2883_);
lean_dec_ref(v_fst_2863_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v_val_2883_);
v___x_2885_ = v___x_2861_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_val_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v___x_2854_);
lean_dec(v_stx_2296_);
v_a_2890_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2858_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2858_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2898_ = l_Lean_Syntax_getArg(v___x_2849_, v___x_2739_);
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
v___x_2900_ = l_Lean_Syntax_isOfKind(v___x_2898_, v___x_2899_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v_env_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec(v___x_2849_);
lean_dec(v_val_2848_);
v___x_2901_ = lean_st_ref_get(v___y_2746_);
v_env_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc_ref(v_env_2902_);
lean_dec(v___x_2901_);
lean_inc_n(v_stx_2296_, 2);
v___x_2903_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2904_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2905_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2904_, v_env_2902_, v___x_2903_);
v___x_2906_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2907_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2905_, v___x_2906_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___x_2905_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2938_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2938_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2938_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v_fst_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2936_; 
v_fst_2912_ = lean_ctor_get(v_a_2908_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_2936_ == 0)
{
lean_object* v_unused_2937_; 
v_unused_2937_ = lean_ctor_get(v_a_2908_, 1);
lean_dec(v_unused_2937_);
v___x_2914_ = v_a_2908_;
v_isShared_2915_ = v_isSharedCheck_2936_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_fst_2912_);
lean_dec(v_a_2908_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2936_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
if (lean_obj_tag(v_fst_2912_) == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; 
lean_del_object(v___x_2910_);
v___x_2916_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2917_ = l_Lean_MessageData_ofName(v___x_2903_);
lean_inc_ref(v___x_2917_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set_tag(v___x_2914_, 7);
lean_ctor_set(v___x_2914_, 1, v___x_2917_);
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2919_ = v___x_2914_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2920_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2923_ = l_Lean_indentD(v___x_2922_);
v___x_2924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2921_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v___x_2917_);
v___x_2928_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2927_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2929_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2930_;
}
}
else
{
lean_object* v_val_2932_; lean_object* v___x_2934_; 
lean_del_object(v___x_2914_);
lean_dec(v___x_2903_);
lean_dec(v_stx_2296_);
v_val_2932_ = lean_ctor_get(v_fst_2912_, 0);
lean_inc(v_val_2932_);
lean_dec_ref(v_fst_2912_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v_val_2932_);
v___x_2934_ = v___x_2910_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_val_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v___x_2903_);
lean_dec(v_stx_2296_);
v_a_2939_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2907_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2907_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_dec(v_stx_2296_);
v___x_2947_ = lean_unsigned_to_nat(3u);
v___x_2948_ = l_Lean_Syntax_getArg(v___x_2849_, v___x_2947_);
lean_dec(v___x_2849_);
v___x_2949_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2948_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; size_t v_sz_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v_sz_2951_ = lean_array_size(v_val_2848_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2848_, v_sz_2951_, v___x_2800_, v_a_2950_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v_val_2848_);
return v___x_2952_;
}
else
{
lean_dec(v_val_2848_);
return v___x_2949_;
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
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v_stx_2296_);
v___x_3003_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec(v_stx_2296_);
v___x_3005_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v_stx_2296_);
v___x_3007_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_stx_2296_);
v___x_3009_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; size_t v_sz_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3011_ = lean_unsigned_to_nat(2u);
v___x_3012_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3011_);
v___x_3013_ = l_Lean_Syntax_getArgs(v___x_3012_);
lean_dec(v___x_3012_);
v_sz_3014_ = lean_array_size(v___x_3013_);
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3014_, v___x_3015_, v___x_3013_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v___x_3017_; lean_object* v_env_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3017_ = lean_st_ref_get(v_a_2302_);
v_env_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_env_3018_);
lean_dec(v___x_3017_);
lean_inc_n(v_stx_2296_, 2);
v___x_3019_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3020_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3021_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3020_, v_env_3018_, v___x_3019_);
v___x_3022_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3023_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3021_, v___x_3022_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3021_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3054_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3054_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3054_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_fst_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3052_; 
v_fst_3028_ = lean_ctor_get(v_a_3024_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v_a_3024_, 1);
lean_dec(v_unused_3053_);
v___x_3030_ = v_a_3024_;
v_isShared_3031_ = v_isSharedCheck_3052_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_fst_3028_);
lean_dec(v_a_3024_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3052_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
if (lean_obj_tag(v_fst_3028_) == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_del_object(v___x_3026_);
v___x_3032_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3033_ = l_Lean_MessageData_ofName(v___x_3019_);
lean_inc_ref(v___x_3033_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 7);
lean_ctor_set(v___x_3030_, 1, v___x_3033_);
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3036_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3039_ = l_Lean_indentD(v___x_3038_);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3037_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3033_);
v___x_3044_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3045_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3046_;
}
}
else
{
lean_object* v_val_3048_; lean_object* v___x_3050_; 
lean_del_object(v___x_3030_);
lean_dec(v___x_3019_);
lean_dec(v_stx_2296_);
v_val_3048_ = lean_ctor_get(v_fst_3028_, 0);
lean_inc(v_val_3048_);
lean_dec_ref(v_fst_3028_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_val_3048_);
v___x_3050_ = v___x_3026_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_val_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v___x_3019_);
lean_dec(v_stx_2296_);
v_a_3055_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3023_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3023_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3197_; 
v_val_3063_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3065_ = v___x_3016_;
v_isShared_3066_ = v_isSharedCheck_3197_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_val_3063_);
lean_dec(v___x_3016_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3197_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v_finSeq_x3f_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3067_ = lean_unsigned_to_nat(1u);
v___x_3068_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3067_);
v___x_3092_ = lean_unsigned_to_nat(3u);
v___x_3093_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3092_);
v___x_3094_ = l_Lean_Syntax_isNone(v___x_3093_);
if (v___x_3094_ == 0)
{
uint8_t v___x_3095_; 
lean_inc(v___x_3093_);
v___x_3095_ = l_Lean_Syntax_matchesNull(v___x_3093_, v___x_3067_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v_env_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_dec(v___x_3093_);
lean_dec(v___x_3068_);
lean_del_object(v___x_3065_);
lean_dec(v_val_3063_);
v___x_3096_ = lean_st_ref_get(v_a_2302_);
v_env_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc_ref(v_env_3097_);
lean_dec(v___x_3096_);
lean_inc_n(v_stx_2296_, 2);
v___x_3098_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3099_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3100_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3099_, v_env_3097_, v___x_3098_);
v___x_3101_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3102_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3100_, v___x_3101_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3100_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3133_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3133_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3133_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_fst_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3131_; 
v_fst_3107_ = lean_ctor_get(v_a_3103_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3103_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v_a_3103_, 1);
lean_dec(v_unused_3132_);
v___x_3109_ = v_a_3103_;
v_isShared_3110_ = v_isSharedCheck_3131_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_fst_3107_);
lean_dec(v_a_3103_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3131_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
if (lean_obj_tag(v_fst_3107_) == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
lean_del_object(v___x_3105_);
v___x_3111_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3112_ = l_Lean_MessageData_ofName(v___x_3098_);
lean_inc_ref(v___x_3112_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set_tag(v___x_3109_, 7);
lean_ctor_set(v___x_3109_, 1, v___x_3112_);
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3115_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3118_ = l_Lean_indentD(v___x_3117_);
v___x_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3116_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3112_);
v___x_3123_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3122_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3124_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3125_;
}
}
else
{
lean_object* v_val_3127_; lean_object* v___x_3129_; 
lean_del_object(v___x_3109_);
lean_dec(v___x_3098_);
lean_dec(v_stx_2296_);
v_val_3127_ = lean_ctor_get(v_fst_3107_, 0);
lean_inc(v_val_3127_);
lean_dec_ref(v_fst_3107_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v_val_3127_);
v___x_3129_ = v___x_3105_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_val_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v___x_3098_);
lean_dec(v_stx_2296_);
v_a_3134_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3102_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3102_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = l_Lean_Syntax_getArg(v___x_3093_, v___x_3142_);
lean_dec(v___x_3093_);
v___x_3144_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_3143_);
v___x_3145_ = l_Lean_Syntax_isOfKind(v___x_3143_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v_env_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v___x_3143_);
lean_dec(v___x_3068_);
lean_del_object(v___x_3065_);
lean_dec(v_val_3063_);
v___x_3146_ = lean_st_ref_get(v_a_2302_);
v_env_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_env_3147_);
lean_dec(v___x_3146_);
lean_inc_n(v_stx_2296_, 2);
v___x_3148_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3149_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3150_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3149_, v_env_3147_, v___x_3148_);
v___x_3151_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3152_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3150_, v___x_3151_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3150_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3183_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3183_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3183_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_fst_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3181_; 
v_fst_3157_ = lean_ctor_get(v_a_3153_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_a_3153_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v_a_3153_, 1);
lean_dec(v_unused_3182_);
v___x_3159_ = v_a_3153_;
v_isShared_3160_ = v_isSharedCheck_3181_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_fst_3157_);
lean_dec(v_a_3153_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3181_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
if (lean_obj_tag(v_fst_3157_) == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_del_object(v___x_3155_);
v___x_3161_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3162_ = l_Lean_MessageData_ofName(v___x_3148_);
lean_inc_ref(v___x_3162_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set_tag(v___x_3159_, 7);
lean_ctor_set(v___x_3159_, 1, v___x_3162_);
lean_ctor_set(v___x_3159_, 0, v___x_3161_);
v___x_3164_ = v___x_3159_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3165_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3168_ = l_Lean_indentD(v___x_3167_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3166_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v___x_3162_);
v___x_3173_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3174_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3175_;
}
}
else
{
lean_object* v_val_3177_; lean_object* v___x_3179_; 
lean_del_object(v___x_3159_);
lean_dec(v___x_3148_);
lean_dec(v_stx_2296_);
v_val_3177_ = lean_ctor_get(v_fst_3157_, 0);
lean_inc(v_val_3177_);
lean_dec_ref(v_fst_3157_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v_val_3177_);
v___x_3179_ = v___x_3155_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_val_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec(v___x_3148_);
lean_dec(v_stx_2296_);
v_a_3184_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3152_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3152_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec(v_stx_2296_);
v___x_3192_ = l_Lean_Syntax_getArg(v___x_3143_, v___x_3067_);
lean_dec(v___x_3143_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3192_);
v___x_3194_ = v___x_3065_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
v_finSeq_x3f_3070_ = v___x_3194_;
v___y_3071_ = v_a_2297_;
v___y_3072_ = v_a_2298_;
v___y_3073_ = v_a_2299_;
v___y_3074_ = v_a_2300_;
v___y_3075_ = v_a_2301_;
v___y_3076_ = v_a_2302_;
goto v___jp_3069_;
}
}
}
}
else
{
lean_object* v___x_3196_; 
lean_dec(v___x_3093_);
lean_del_object(v___x_3065_);
lean_dec(v_stx_2296_);
v___x_3196_ = lean_box(0);
v_finSeq_x3f_3070_ = v___x_3196_;
v___y_3071_ = v_a_2297_;
v___y_3072_ = v_a_2298_;
v___y_3073_ = v_a_2299_;
v___y_3074_ = v_a_2300_;
v___y_3075_ = v_a_2301_;
v___y_3076_ = v_a_2302_;
goto v___jp_3069_;
}
v___jp_3069_:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3068_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; size_t v_sz_3079_; lean_object* v___x_3080_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref(v___x_3077_);
v_sz_3079_ = lean_array_size(v_val_3063_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3063_, v_sz_3079_, v___x_3015_, v_a_3078_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v_val_3063_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3091_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3087_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3081_, v_a_3083_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
else
{
lean_dec(v_a_3081_);
return v___x_3082_;
}
}
else
{
lean_dec(v_finSeq_x3f_3070_);
return v___x_3080_;
}
}
else
{
lean_dec(v_finSeq_x3f_3070_);
lean_dec(v_val_3063_);
return v___x_3077_;
}
}
}
}
}
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_unsigned_to_nat(1u);
v___x_3199_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3198_);
lean_dec(v_stx_2296_);
v___x_3200_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3199_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3222_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3222_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3222_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
uint8_t v_breaks_3205_; uint8_t v_returnsEarly_3206_; lean_object* v_reassigns_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3220_; 
v_breaks_3205_ = lean_ctor_get_uint8(v_a_3201_, sizeof(void*)*2);
v_returnsEarly_3206_ = lean_ctor_get_uint8(v_a_3201_, sizeof(void*)*2 + 2);
v_reassigns_3207_ = lean_ctor_get(v_a_3201_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_a_3201_, 0);
lean_dec(v_unused_3221_);
v___x_3209_ = v_a_3201_;
v_isShared_3210_ = v_isSharedCheck_3220_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_reassigns_3207_);
lean_dec(v_a_3201_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3220_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___y_3212_; 
if (v_breaks_3205_ == 0)
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_unsigned_to_nat(0u);
v___y_3212_ = v___x_3219_;
goto v___jp_3211_;
}
else
{
v___y_3212_ = v___x_3198_;
goto v___jp_3211_;
}
v___jp_3211_:
{
lean_object* v___x_3214_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___y_3212_);
v___x_3214_ = v___x_3209_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___y_3212_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_reassigns_3207_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*2 + 2, v_returnsEarly_3206_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
lean_ctor_set_uint8(v___x_3214_, sizeof(void*)*2, v___x_2623_);
lean_ctor_set_uint8(v___x_3214_, sizeof(void*)*2 + 1, v___x_2623_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3214_);
v___x_3216_ = v___x_3203_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
else
{
return v___x_3200_;
}
}
}
else
{
lean_object* v___x_3223_; lean_object* v___y_3225_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3296_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3223_);
v___x_3297_ = l_Lean_Syntax_getArgs(v___x_3296_);
lean_dec(v___x_3296_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3300_ = lean_array_get_size(v___x_3297_);
v___x_3301_ = lean_nat_dec_lt(v___x_3298_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_dec_ref(v___x_3297_);
v___y_3225_ = v___x_3299_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3302_ = lean_box(v___x_2623_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3299_);
v___x_3304_ = lean_nat_dec_le(v___x_3300_, v___x_3300_);
if (v___x_3304_ == 0)
{
if (v___x_3301_ == 0)
{
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3297_);
v___y_3225_ = v___x_3299_;
goto v___jp_3224_;
}
else
{
size_t v___x_3305_; size_t v___x_3306_; lean_object* v___x_3307_; lean_object* v_snd_3308_; 
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = lean_usize_of_nat(v___x_3300_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2623_, v___x_2621_, v___x_3297_, v___x_3305_, v___x_3306_, v___x_3303_);
lean_dec_ref(v___x_3297_);
v_snd_3308_ = lean_ctor_get(v___x_3307_, 1);
lean_inc(v_snd_3308_);
lean_dec_ref(v___x_3307_);
v___y_3225_ = v_snd_3308_;
goto v___jp_3224_;
}
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; lean_object* v_snd_3312_; 
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = lean_usize_of_nat(v___x_3300_);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2623_, v___x_2621_, v___x_3297_, v___x_3309_, v___x_3310_, v___x_3303_);
lean_dec_ref(v___x_3297_);
v_snd_3312_ = lean_ctor_get(v___x_3311_, 1);
lean_inc(v_snd_3312_);
lean_dec_ref(v___x_3311_);
v___y_3225_ = v_snd_3312_;
goto v___jp_3224_;
}
}
v___jp_3224_:
{
size_t v_sz_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v_sz_3226_ = lean_array_size(v___y_3225_);
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3226_, v___x_3227_, v___y_3225_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v___x_3229_; lean_object* v_env_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3229_ = lean_st_ref_get(v_a_2302_);
v_env_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc_ref(v_env_3230_);
lean_dec(v___x_3229_);
lean_inc_n(v_stx_2296_, 2);
v___x_3231_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3232_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3233_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3232_, v_env_3230_, v___x_3231_);
v___x_3234_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3235_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3233_, v___x_3234_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3233_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3266_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v_fst_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3264_; 
v_fst_3240_ = lean_ctor_get(v_a_3236_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3236_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_a_3236_, 1);
lean_dec(v_unused_3265_);
v___x_3242_ = v_a_3236_;
v_isShared_3243_ = v_isSharedCheck_3264_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_fst_3240_);
lean_dec(v_a_3236_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3264_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
if (lean_obj_tag(v_fst_3240_) == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_del_object(v___x_3238_);
v___x_3244_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3245_ = l_Lean_MessageData_ofName(v___x_3231_);
lean_inc_ref(v___x_3245_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 7);
lean_ctor_set(v___x_3242_, 1, v___x_3245_);
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3247_ = v___x_3242_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3248_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3251_ = l_Lean_indentD(v___x_3250_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3249_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3245_);
v___x_3256_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3257_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3258_;
}
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; 
lean_del_object(v___x_3242_);
lean_dec(v___x_3231_);
lean_dec(v_stx_2296_);
v_val_3260_ = lean_ctor_get(v_fst_3240_, 0);
lean_inc(v_val_3260_);
lean_dec_ref(v_fst_3240_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v_val_3260_);
v___x_3262_ = v___x_3238_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_val_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v___x_3231_);
lean_dec(v_stx_2296_);
v_a_3267_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3235_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3235_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec_ref(v___x_3228_);
v___x_3275_ = lean_unsigned_to_nat(3u);
v___x_3276_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3275_);
lean_dec(v_stx_2296_);
v___x_3277_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3276_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3295_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3295_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3295_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
uint8_t v_returnsEarly_3282_; lean_object* v_reassigns_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3293_; 
v_returnsEarly_3282_ = lean_ctor_get_uint8(v_a_3278_, sizeof(void*)*2 + 2);
v_reassigns_3283_ = lean_ctor_get(v_a_3278_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_a_3278_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v_a_3278_, 0);
lean_dec(v_unused_3294_);
v___x_3285_ = v_a_3278_;
v_isShared_3286_ = v_isSharedCheck_3293_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_reassigns_3283_);
lean_dec(v_a_3278_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3293_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3223_);
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_reassigns_3283_);
lean_ctor_set_uint8(v_reuseFailAlloc_3292_, sizeof(void*)*2 + 2, v_returnsEarly_3282_);
v___x_3288_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3290_; 
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*2, v___x_2621_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*2 + 1, v___x_2621_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3288_);
v___x_3290_ = v___x_3280_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
return v___x_3277_;
}
}
}
}
}
else
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3313_ = lean_unsigned_to_nat(1u);
v___x_3314_ = lean_unsigned_to_nat(3u);
v___x_3315_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3314_);
lean_dec(v_stx_2296_);
v___x_3316_ = l_Lean_NameSet_empty;
v___x_3317_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3317_, 0, v___x_3313_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*2, v___x_2619_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*2 + 1, v___x_2619_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*2 + 2, v___x_2619_);
v___x_3318_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3315_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3327_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
v___x_3323_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3317_, v_a_3319_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
else
{
lean_dec_ref(v___x_3317_);
return v___x_3318_;
}
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; size_t v_sz_3331_; size_t v___x_3332_; lean_object* v___x_3333_; 
v___x_3328_ = lean_unsigned_to_nat(4u);
v___x_3329_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3328_);
v___x_3330_ = l_Lean_Syntax_getArgs(v___x_3329_);
lean_dec(v___x_3329_);
v_sz_3331_ = lean_array_size(v___x_3330_);
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3331_, v___x_3332_, v___x_3330_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; lean_object* v_env_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3334_ = lean_st_ref_get(v_a_2302_);
v_env_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc_ref(v_env_3335_);
lean_dec(v___x_3334_);
lean_inc_n(v_stx_2296_, 2);
v___x_3336_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3337_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3338_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3337_, v_env_3335_, v___x_3336_);
v___x_3339_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3340_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3338_, v___x_3339_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3338_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3371_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3371_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3371_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_fst_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3369_; 
v_fst_3345_ = lean_ctor_get(v_a_3341_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_a_3341_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v_a_3341_, 1);
lean_dec(v_unused_3370_);
v___x_3347_ = v_a_3341_;
v_isShared_3348_ = v_isSharedCheck_3369_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_fst_3345_);
lean_dec(v_a_3341_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3369_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
if (lean_obj_tag(v_fst_3345_) == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3352_; 
lean_del_object(v___x_3343_);
v___x_3349_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3350_ = l_Lean_MessageData_ofName(v___x_3336_);
lean_inc_ref(v___x_3350_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 7);
lean_ctor_set(v___x_3347_, 1, v___x_3350_);
lean_ctor_set(v___x_3347_, 0, v___x_3349_);
v___x_3352_ = v___x_3347_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3353_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3356_ = l_Lean_indentD(v___x_3355_);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3354_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
lean_ctor_set(v___x_3360_, 1, v___x_3350_);
v___x_3361_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3362_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3363_;
}
}
else
{
lean_object* v_val_3365_; lean_object* v___x_3367_; 
lean_del_object(v___x_3347_);
lean_dec(v___x_3336_);
lean_dec(v_stx_2296_);
v_val_3365_ = lean_ctor_get(v_fst_3345_, 0);
lean_inc(v_val_3365_);
lean_dec_ref(v_fst_3345_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 0, v_val_3365_);
v___x_3367_ = v___x_3343_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_val_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec(v___x_3336_);
lean_dec(v_stx_2296_);
v_a_3372_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3340_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3340_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_val_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3467_; 
v_val_3380_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3382_ = v___x_3333_;
v_isShared_3383_ = v_isSharedCheck_3467_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_val_3380_);
lean_dec(v___x_3333_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3467_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v_elseSeq_x3f_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3384_ = lean_unsigned_to_nat(3u);
v___x_3385_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3384_);
v___x_3410_ = lean_unsigned_to_nat(5u);
v___x_3411_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3410_);
v___x_3412_ = l_Lean_Syntax_isNone(v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3413_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3411_);
v___x_3414_ = l_Lean_Syntax_matchesNull(v___x_3411_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v_env_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec(v___x_3411_);
lean_dec(v___x_3385_);
lean_del_object(v___x_3382_);
lean_dec(v_val_3380_);
v___x_3415_ = lean_st_ref_get(v_a_2302_);
v_env_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc_ref(v_env_3416_);
lean_dec(v___x_3415_);
lean_inc_n(v_stx_2296_, 2);
v___x_3417_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3418_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3419_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3418_, v_env_3416_, v___x_3417_);
v___x_3420_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3421_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3419_, v___x_3420_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3419_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3452_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3452_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3452_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_fst_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3450_; 
v_fst_3426_ = lean_ctor_get(v_a_3422_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_a_3422_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v_a_3422_, 1);
lean_dec(v_unused_3451_);
v___x_3428_ = v_a_3422_;
v_isShared_3429_ = v_isSharedCheck_3450_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_fst_3426_);
lean_dec(v_a_3422_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3450_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
if (lean_obj_tag(v_fst_3426_) == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_del_object(v___x_3424_);
v___x_3430_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3431_ = l_Lean_MessageData_ofName(v___x_3417_);
lean_inc_ref(v___x_3431_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set_tag(v___x_3428_, 7);
lean_ctor_set(v___x_3428_, 1, v___x_3431_);
lean_ctor_set(v___x_3428_, 0, v___x_3430_);
v___x_3433_ = v___x_3428_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3430_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3434_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3433_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3437_ = l_Lean_indentD(v___x_3436_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v___x_3431_);
v___x_3442_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3443_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3444_;
}
}
else
{
lean_object* v_val_3446_; lean_object* v___x_3448_; 
lean_del_object(v___x_3428_);
lean_dec(v___x_3417_);
lean_dec(v_stx_2296_);
v_val_3446_ = lean_ctor_get(v_fst_3426_, 0);
lean_inc(v_val_3446_);
lean_dec_ref(v_fst_3426_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v_val_3446_);
v___x_3448_ = v___x_3424_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_val_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v___x_3417_);
lean_dec(v_stx_2296_);
v_a_3453_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3421_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3421_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec(v_stx_2296_);
v___x_3461_ = lean_unsigned_to_nat(1u);
v___x_3462_ = l_Lean_Syntax_getArg(v___x_3411_, v___x_3461_);
lean_dec(v___x_3411_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3462_);
v___x_3464_ = v___x_3382_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
v_elseSeq_x3f_3387_ = v___x_3464_;
v___y_3388_ = v_a_2297_;
v___y_3389_ = v_a_2298_;
v___y_3390_ = v_a_2299_;
v___y_3391_ = v_a_2300_;
v___y_3392_ = v_a_2301_;
v___y_3393_ = v_a_2302_;
goto v___jp_3386_;
}
}
}
else
{
lean_object* v___x_3466_; 
lean_dec(v___x_3411_);
lean_del_object(v___x_3382_);
lean_dec(v_stx_2296_);
v___x_3466_ = lean_box(0);
v_elseSeq_x3f_3387_ = v___x_3466_;
v___y_3388_ = v_a_2297_;
v___y_3389_ = v_a_2298_;
v___y_3390_ = v_a_2299_;
v___y_3391_ = v_a_2300_;
v___y_3392_ = v_a_2301_;
v___y_3393_ = v_a_2302_;
goto v___jp_3386_;
}
v___jp_3386_:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; size_t v_sz_3397_; lean_object* v___x_3398_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = l_Array_reverse___redArg(v_val_3380_);
v_sz_3397_ = lean_array_size(v___x_3396_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3396_, v_sz_3397_, v___x_3332_, v_a_3395_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec_ref(v___x_3396_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3385_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3409_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3401_, v_a_3399_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3405_);
v___x_3407_ = v___x_3403_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
else
{
lean_dec(v_a_3399_);
return v___x_3400_;
}
}
else
{
lean_dec(v___x_3385_);
return v___x_3398_;
}
}
else
{
lean_dec(v___x_3385_);
lean_dec(v_val_3380_);
return v___x_3394_;
}
}
}
}
}
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_unsigned_to_nat(1u);
v___x_3640_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3469_);
v___x_3641_ = l_Lean_Syntax_isNone(v___x_3640_);
if (v___x_3641_ == 0)
{
uint8_t v___x_3642_; 
lean_inc(v___x_3640_);
v___x_3642_ = l_Lean_Syntax_matchesNull(v___x_3640_, v___x_3469_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v_env_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec(v___x_3640_);
v___x_3643_ = lean_st_ref_get(v_a_2302_);
v_env_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc_ref(v_env_3644_);
lean_dec(v___x_3643_);
lean_inc_n(v_stx_2296_, 2);
v___x_3645_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3646_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3647_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3646_, v_env_3644_, v___x_3645_);
v___x_3648_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3649_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3647_, v___x_3648_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3647_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3680_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3680_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3680_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_fst_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3678_; 
v_fst_3654_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; 
v_unused_3679_ = lean_ctor_get(v_a_3650_, 1);
lean_dec(v_unused_3679_);
v___x_3656_ = v_a_3650_;
v_isShared_3657_ = v_isSharedCheck_3678_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_fst_3654_);
lean_dec(v_a_3650_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3678_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_del_object(v___x_3652_);
v___x_3658_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3659_ = l_Lean_MessageData_ofName(v___x_3645_);
lean_inc_ref(v___x_3659_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 7);
lean_ctor_set(v___x_3656_, 1, v___x_3659_);
lean_ctor_set(v___x_3656_, 0, v___x_3658_);
v___x_3661_ = v___x_3656_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3662_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3665_ = l_Lean_indentD(v___x_3664_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3663_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
lean_ctor_set(v___x_3669_, 1, v___x_3659_);
v___x_3670_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3669_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3671_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3672_;
}
}
else
{
lean_object* v_val_3674_; lean_object* v___x_3676_; 
lean_del_object(v___x_3656_);
lean_dec(v___x_3645_);
lean_dec(v_stx_2296_);
v_val_3674_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3674_);
lean_dec_ref(v_fst_3654_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3674_);
v___x_3676_ = v___x_3652_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_val_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec(v___x_3645_);
lean_dec(v_stx_2296_);
v_a_3681_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3649_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3649_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3689_ = l_Lean_Syntax_getArg(v___x_3640_, v___x_3468_);
lean_dec(v___x_3640_);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
v___x_3691_ = l_Lean_Syntax_isOfKind(v___x_3689_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; lean_object* v_env_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3692_ = lean_st_ref_get(v_a_2302_);
v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_ref(v_env_3693_);
lean_dec(v___x_3692_);
lean_inc_n(v_stx_2296_, 2);
v___x_3694_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3695_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3696_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3695_, v_env_3693_, v___x_3694_);
v___x_3697_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3698_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3696_, v___x_3697_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3696_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3729_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_fst_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3727_; 
v_fst_3703_ = lean_ctor_get(v_a_3699_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_a_3699_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v_a_3699_, 1);
lean_dec(v_unused_3728_);
v___x_3705_ = v_a_3699_;
v_isShared_3706_ = v_isSharedCheck_3727_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_fst_3703_);
lean_dec(v_a_3699_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3727_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
if (lean_obj_tag(v_fst_3703_) == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_del_object(v___x_3701_);
v___x_3707_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3708_ = l_Lean_MessageData_ofName(v___x_3694_);
lean_inc_ref(v___x_3708_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 7);
lean_ctor_set(v___x_3705_, 1, v___x_3708_);
lean_ctor_set(v___x_3705_, 0, v___x_3707_);
v___x_3710_ = v___x_3705_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3711_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3714_ = l_Lean_indentD(v___x_3713_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3712_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
lean_ctor_set(v___x_3718_, 1, v___x_3708_);
v___x_3719_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3720_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3721_;
}
}
else
{
lean_object* v_val_3723_; lean_object* v___x_3725_; 
lean_del_object(v___x_3705_);
lean_dec(v___x_3694_);
lean_dec(v_stx_2296_);
v_val_3723_ = lean_ctor_get(v_fst_3703_, 0);
lean_inc(v_val_3723_);
lean_dec_ref(v_fst_3703_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v_val_3723_);
v___x_3725_ = v___x_3701_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_val_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v___x_3694_);
lean_dec(v_stx_2296_);
v_a_3730_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3698_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3698_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
v___y_3535_ = v_a_2297_;
v___y_3536_ = v_a_2298_;
v___y_3537_ = v_a_2299_;
v___y_3538_ = v_a_2300_;
v___y_3539_ = v_a_2301_;
v___y_3540_ = v_a_2302_;
goto v___jp_3534_;
}
}
}
else
{
lean_dec(v___x_3640_);
v___y_3535_ = v_a_2297_;
v___y_3536_ = v_a_2298_;
v___y_3537_ = v_a_2299_;
v___y_3538_ = v_a_2300_;
v___y_3539_ = v_a_2301_;
v___y_3540_ = v_a_2302_;
goto v___jp_3534_;
}
v___jp_3470_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3477_ = lean_unsigned_to_nat(6u);
v___x_3478_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3477_);
v___x_3479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3478_);
v___x_3480_ = l_Lean_Syntax_isOfKind(v___x_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v_env_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v___x_3478_);
v___x_3481_ = lean_st_ref_get(v___y_3476_);
v_env_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc_ref(v_env_3482_);
lean_dec(v___x_3481_);
lean_inc_n(v_stx_2296_, 2);
v___x_3483_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3484_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3485_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3484_, v_env_3482_, v___x_3483_);
v___x_3486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3487_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3485_, v___x_3486_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___x_3485_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3518_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3518_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3518_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v_fst_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3516_; 
v_fst_3492_ = lean_ctor_get(v_a_3488_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_a_3488_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; 
v_unused_3517_ = lean_ctor_get(v_a_3488_, 1);
lean_dec(v_unused_3517_);
v___x_3494_ = v_a_3488_;
v_isShared_3495_ = v_isSharedCheck_3516_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_fst_3492_);
lean_dec(v_a_3488_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3516_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
if (lean_obj_tag(v_fst_3492_) == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_del_object(v___x_3490_);
v___x_3496_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3497_ = l_Lean_MessageData_ofName(v___x_3483_);
lean_inc_ref(v___x_3497_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 7);
lean_ctor_set(v___x_3494_, 1, v___x_3497_);
lean_ctor_set(v___x_3494_, 0, v___x_3496_);
v___x_3499_ = v___x_3494_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3500_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3503_ = l_Lean_indentD(v___x_3502_);
v___x_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3501_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___x_3497_);
v___x_3508_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3507_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3509_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3510_;
}
}
else
{
lean_object* v_val_3512_; lean_object* v___x_3514_; 
lean_del_object(v___x_3494_);
lean_dec(v___x_3483_);
lean_dec(v_stx_2296_);
v_val_3512_ = lean_ctor_get(v_fst_3492_, 0);
lean_inc(v_val_3512_);
lean_dec_ref(v_fst_3492_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v_val_3512_);
v___x_3514_ = v___x_3490_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_val_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v___x_3483_);
lean_dec(v_stx_2296_);
v_a_3519_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3487_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3487_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; size_t v_sz_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
lean_dec(v_stx_2296_);
v___x_3527_ = l_Lean_Syntax_getArg(v___x_3478_, v___x_3468_);
lean_dec(v___x_3478_);
v___x_3528_ = l_Lean_Syntax_getArgs(v___x_3527_);
lean_dec(v___x_3527_);
v___x_3529_ = l_Lean_NameSet_empty;
v___x_3530_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3530_, 0, v___x_3469_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*2, v___x_2615_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*2 + 1, v___x_2615_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*2 + 2, v___x_2615_);
v_sz_3531_ = lean_array_size(v___x_3528_);
v___x_3532_ = ((size_t)0ULL);
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2615_, v___x_3528_, v_sz_3531_, v___x_3532_, v___x_3530_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec_ref(v___x_3528_);
return v___x_3533_;
}
}
v___jp_3534_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(2u);
v___x_3542_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3541_);
v___x_3543_ = l_Lean_Syntax_isNone(v___x_3542_);
if (v___x_3543_ == 0)
{
uint8_t v___x_3544_; 
lean_inc(v___x_3542_);
v___x_3544_ = l_Lean_Syntax_matchesNull(v___x_3542_, v___x_3469_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v_env_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v___x_3542_);
v___x_3545_ = lean_st_ref_get(v___y_3540_);
v_env_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc_ref(v_env_3546_);
lean_dec(v___x_3545_);
lean_inc_n(v_stx_2296_, 2);
v___x_3547_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3548_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3549_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3548_, v_env_3546_, v___x_3547_);
v___x_3550_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3551_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3549_, v___x_3550_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___x_3549_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3582_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3582_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3582_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v_fst_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3580_; 
v_fst_3556_ = lean_ctor_get(v_a_3552_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3552_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_a_3552_, 1);
lean_dec(v_unused_3581_);
v___x_3558_ = v_a_3552_;
v_isShared_3559_ = v_isSharedCheck_3580_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_fst_3556_);
lean_dec(v_a_3552_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3580_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
if (lean_obj_tag(v_fst_3556_) == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_del_object(v___x_3554_);
v___x_3560_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3561_ = l_Lean_MessageData_ofName(v___x_3547_);
lean_inc_ref(v___x_3561_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 7);
lean_ctor_set(v___x_3558_, 1, v___x_3561_);
lean_ctor_set(v___x_3558_, 0, v___x_3560_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3564_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3567_ = l_Lean_indentD(v___x_3566_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3565_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v___x_3561_);
v___x_3572_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3573_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3574_;
}
}
else
{
lean_object* v_val_3576_; lean_object* v___x_3578_; 
lean_del_object(v___x_3558_);
lean_dec(v___x_3547_);
lean_dec(v_stx_2296_);
v_val_3576_ = lean_ctor_get(v_fst_3556_, 0);
lean_inc(v_val_3576_);
lean_dec_ref(v_fst_3556_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_val_3576_);
v___x_3578_ = v___x_3554_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_val_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___x_3547_);
lean_dec(v_stx_2296_);
v_a_3583_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3551_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3551_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3591_ = l_Lean_Syntax_getArg(v___x_3542_, v___x_3468_);
lean_dec(v___x_3542_);
v___x_3592_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3593_ = l_Lean_Syntax_isOfKind(v___x_3591_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v_env_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3594_ = lean_st_ref_get(v___y_3540_);
v_env_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_ref(v_env_3595_);
lean_dec(v___x_3594_);
lean_inc_n(v_stx_2296_, 2);
v___x_3596_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3597_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3598_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3597_, v_env_3595_, v___x_3596_);
v___x_3599_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3600_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3598_, v___x_3599_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___x_3598_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3631_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3631_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3631_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_fst_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3629_; 
v_fst_3605_ = lean_ctor_get(v_a_3601_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_a_3601_, 1);
lean_dec(v_unused_3630_);
v___x_3607_ = v_a_3601_;
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_fst_3605_);
lean_dec(v_a_3601_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
if (lean_obj_tag(v_fst_3605_) == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_del_object(v___x_3603_);
v___x_3609_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3610_ = l_Lean_MessageData_ofName(v___x_3596_);
lean_inc_ref(v___x_3610_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 7);
lean_ctor_set(v___x_3607_, 1, v___x_3610_);
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3612_ = v___x_3607_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3613_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3616_ = l_Lean_indentD(v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3610_);
v___x_3621_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3622_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3623_;
}
}
else
{
lean_object* v_val_3625_; lean_object* v___x_3627_; 
lean_del_object(v___x_3607_);
lean_dec(v___x_3596_);
lean_dec(v_stx_2296_);
v_val_3625_ = lean_ctor_get(v_fst_3605_, 0);
lean_inc(v_val_3625_);
lean_dec_ref(v_fst_3605_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v_val_3625_);
v___x_3627_ = v___x_3603_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_val_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v___x_3596_);
lean_dec(v_stx_2296_);
v_a_3632_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3600_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3600_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
v___y_3471_ = v___y_3535_;
v___y_3472_ = v___y_3536_;
v___y_3473_ = v___y_3537_;
v___y_3474_ = v___y_3538_;
v___y_3475_ = v___y_3539_;
v___y_3476_ = v___y_3540_;
goto v___jp_3470_;
}
}
}
else
{
lean_dec(v___x_3542_);
v___y_3471_ = v___y_3535_;
v___y_3472_ = v___y_3536_;
v___y_3473_ = v___y_3537_;
v___y_3474_ = v___y_3538_;
v___y_3475_ = v___y_3539_;
v___y_3476_ = v___y_3540_;
goto v___jp_3470_;
}
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3738_);
v___x_3740_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3739_);
v___x_3741_ = l_Lean_Syntax_isOfKind(v___x_3739_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; uint8_t v___x_3743_; 
v___x_3742_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3739_);
v___x_3743_ = l_Lean_Syntax_isOfKind(v___x_3739_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v_env_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec(v___x_3739_);
v___x_3744_ = lean_st_ref_get(v_a_2302_);
v_env_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_env_3745_);
lean_dec(v___x_3744_);
lean_inc_n(v_stx_2296_, 2);
v___x_3746_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3747_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3748_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3747_, v_env_3745_, v___x_3746_);
v___x_3749_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3750_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3748_, v___x_3749_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3748_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3781_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_fst_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3779_; 
v_fst_3755_ = lean_ctor_get(v_a_3751_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3751_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v_a_3751_, 1);
lean_dec(v_unused_3780_);
v___x_3757_ = v_a_3751_;
v_isShared_3758_ = v_isSharedCheck_3779_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_fst_3755_);
lean_dec(v_a_3751_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3779_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
if (lean_obj_tag(v_fst_3755_) == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
lean_del_object(v___x_3753_);
v___x_3759_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3760_ = l_Lean_MessageData_ofName(v___x_3746_);
lean_inc_ref(v___x_3760_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 7);
lean_ctor_set(v___x_3757_, 1, v___x_3760_);
lean_ctor_set(v___x_3757_, 0, v___x_3759_);
v___x_3762_ = v___x_3757_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3763_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3766_ = l_Lean_indentD(v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3764_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v___x_3760_);
v___x_3771_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3772_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3773_;
}
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3777_; 
lean_del_object(v___x_3757_);
lean_dec(v___x_3746_);
lean_dec(v_stx_2296_);
v_val_3775_ = lean_ctor_get(v_fst_3755_, 0);
lean_inc(v_val_3775_);
lean_dec_ref(v_fst_3755_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v_val_3775_);
v___x_3777_ = v___x_3753_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_val_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v___x_3746_);
lean_dec(v_stx_2296_);
v_a_3782_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3750_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3750_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
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
else
{
lean_object* v___x_3790_; 
lean_dec(v_stx_2296_);
v___x_3790_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2533_, v___x_3739_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3790_;
}
}
else
{
lean_object* v___x_3791_; 
lean_dec(v_stx_2296_);
v___x_3791_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2533_, v___x_3739_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3791_;
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3792_);
v___x_3794_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
lean_inc(v___x_3793_);
v___x_3795_ = l_Lean_Syntax_isOfKind(v___x_3793_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; uint8_t v___x_3797_; 
v___x_3796_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
lean_inc(v___x_3793_);
v___x_3797_ = l_Lean_Syntax_isOfKind(v___x_3793_, v___x_3796_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v_env_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
lean_dec(v___x_3793_);
v___x_3798_ = lean_st_ref_get(v_a_2302_);
v_env_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc_ref(v_env_3799_);
lean_dec(v___x_3798_);
lean_inc_n(v_stx_2296_, 2);
v___x_3800_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3801_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3802_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3801_, v_env_3799_, v___x_3800_);
v___x_3803_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3804_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3802_, v___x_3803_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3802_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3835_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3835_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3835_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_fst_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3833_; 
v_fst_3809_ = lean_ctor_get(v_a_3805_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3805_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v_a_3805_, 1);
lean_dec(v_unused_3834_);
v___x_3811_ = v_a_3805_;
v_isShared_3812_ = v_isSharedCheck_3833_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_fst_3809_);
lean_dec(v_a_3805_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3833_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
if (lean_obj_tag(v_fst_3809_) == 0)
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_del_object(v___x_3807_);
v___x_3813_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3814_ = l_Lean_MessageData_ofName(v___x_3800_);
lean_inc_ref(v___x_3814_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set_tag(v___x_3811_, 7);
lean_ctor_set(v___x_3811_, 1, v___x_3814_);
lean_ctor_set(v___x_3811_, 0, v___x_3813_);
v___x_3816_ = v___x_3811_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_3820_ = l_Lean_indentD(v___x_3819_);
v___x_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3818_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v___x_3814_);
v___x_3825_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3826_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3827_;
}
}
else
{
lean_object* v_val_3829_; lean_object* v___x_3831_; 
lean_del_object(v___x_3811_);
lean_dec(v___x_3800_);
lean_dec(v_stx_2296_);
v_val_3829_ = lean_ctor_get(v_fst_3809_, 0);
lean_inc(v_val_3829_);
lean_dec_ref(v_fst_3809_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v_val_3829_);
v___x_3831_ = v___x_3807_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_val_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec(v___x_3800_);
lean_dec(v_stx_2296_);
v_a_3836_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3804_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3804_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
else
{
lean_object* v___x_3844_; 
lean_dec(v_stx_2296_);
v___x_3844_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3793_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3793_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v___x_3846_ = lean_box(0);
v___x_3847_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3845_, v___x_3846_, v___x_3846_, v___x_3846_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3847_;
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
v_a_3848_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3844_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3844_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
else
{
lean_object* v___x_3856_; 
lean_dec(v_stx_2296_);
v___x_3856_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3793_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_3793_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = lean_box(0);
v___x_3859_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3857_, v___x_3858_, v___x_3858_, v___x_3858_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3859_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
v_a_3860_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3856_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3856_);
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
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3868_);
v___x_3870_ = l_Lean_Syntax_isNone(v___x_3869_);
if (v___x_3870_ == 0)
{
uint8_t v___x_3871_; 
v___x_3871_ = l_Lean_Syntax_matchesNull(v___x_3869_, v___x_3868_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v_env_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3872_ = lean_st_ref_get(v_a_2302_);
v_env_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc_ref(v_env_3873_);
lean_dec(v___x_3872_);
lean_inc_n(v_stx_2296_, 2);
v___x_3874_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3875_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3876_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3875_, v_env_3873_, v___x_3874_);
v___x_3877_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3878_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3876_, v___x_3877_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
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
v___x_3893_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
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
v___x_3901_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3900_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3901_;
}
}
else
{
lean_object* v_val_3903_; lean_object* v___x_3905_; 
lean_del_object(v___x_3885_);
lean_dec(v___x_3874_);
lean_dec(v_stx_2296_);
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
lean_dec(v_stx_2296_);
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
v___y_2551_ = v_a_2297_;
v___y_2552_ = v_a_2298_;
v___y_2553_ = v_a_2299_;
v___y_2554_ = v_a_2300_;
v___y_2555_ = v_a_2301_;
v___y_2556_ = v_a_2302_;
goto v___jp_2550_;
}
}
else
{
lean_dec(v___x_3869_);
v___y_2551_ = v_a_2297_;
v___y_2552_ = v_a_2298_;
v___y_2553_ = v_a_2299_;
v___y_2554_ = v_a_2300_;
v___y_2555_ = v_a_2301_;
v___y_2556_ = v_a_2302_;
goto v___jp_2550_;
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3918_);
v___x_3920_ = l_Lean_Syntax_isNone(v___x_3919_);
if (v___x_3920_ == 0)
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_Syntax_matchesNull(v___x_3919_, v___x_3918_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v_env_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3922_ = lean_st_ref_get(v_a_2302_);
v_env_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc_ref(v_env_3923_);
lean_dec(v___x_3922_);
lean_inc_n(v_stx_2296_, 2);
v___x_3924_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3925_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3926_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3925_, v_env_3923_, v___x_3924_);
v___x_3927_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3928_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3926_, v___x_3927_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
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
v___x_3943_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
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
v___x_3951_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3950_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_3951_;
}
}
else
{
lean_object* v_val_3953_; lean_object* v___x_3955_; 
lean_del_object(v___x_3935_);
lean_dec(v___x_3924_);
lean_dec(v_stx_2296_);
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
lean_dec(v_stx_2296_);
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
v___y_2350_ = v_a_2297_;
v___y_2351_ = v_a_2298_;
v___y_2352_ = v_a_2299_;
v___y_2353_ = v_a_2300_;
v___y_2354_ = v_a_2301_;
v___y_2355_ = v_a_2302_;
goto v___jp_2349_;
}
}
else
{
lean_dec(v___x_3919_);
v___y_2350_ = v_a_2297_;
v___y_2351_ = v_a_2298_;
v___y_2352_ = v_a_2299_;
v___y_2353_ = v_a_2300_;
v___y_2354_ = v_a_2301_;
v___y_2355_ = v_a_2302_;
goto v___jp_2349_;
}
}
v___jp_2550_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2557_ = lean_unsigned_to_nat(2u);
v___x_2558_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2557_);
v___x_2559_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2560_ = l_Lean_Syntax_isOfKind(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v_env_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2561_ = lean_st_ref_get(v___y_2556_);
v_env_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_env_2562_);
lean_dec(v___x_2561_);
lean_inc_n(v_stx_2296_, 2);
v___x_2563_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2564_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2565_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2564_, v_env_2562_, v___x_2563_);
v___x_2566_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2567_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2565_, v___x_2566_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___x_2565_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2598_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2598_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2598_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_fst_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2596_; 
v_fst_2572_ = lean_ctor_get(v_a_2568_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_a_2568_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v_a_2568_, 1);
lean_dec(v_unused_2597_);
v___x_2574_ = v_a_2568_;
v_isShared_2575_ = v_isSharedCheck_2596_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_fst_2572_);
lean_dec(v_a_2568_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2596_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
if (lean_obj_tag(v_fst_2572_) == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_del_object(v___x_2570_);
v___x_2576_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2577_ = l_Lean_MessageData_ofName(v___x_2563_);
lean_inc_ref(v___x_2577_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 7);
lean_ctor_set(v___x_2574_, 1, v___x_2577_);
lean_ctor_set(v___x_2574_, 0, v___x_2576_);
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2580_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2583_ = l_Lean_indentD(v___x_2582_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2581_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set(v___x_2587_, 1, v___x_2577_);
v___x_2588_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2589_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2590_;
}
}
else
{
lean_object* v_val_2592_; lean_object* v___x_2594_; 
lean_del_object(v___x_2574_);
lean_dec(v___x_2563_);
lean_dec(v_stx_2296_);
v_val_2592_ = lean_ctor_get(v_fst_2572_, 0);
lean_inc(v_val_2592_);
lean_dec_ref(v_fst_2572_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v_val_2592_);
v___x_2594_ = v___x_2570_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_val_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v___x_2563_);
lean_dec(v_stx_2296_);
v_a_2599_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2567_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2567_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_unsigned_to_nat(3u);
v___x_2608_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2607_);
lean_dec(v_stx_2296_);
v___x_2609_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2549_, v___x_2608_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2609_;
}
}
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_3968_);
v___x_3970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3971_ = l_Lean_Syntax_isOfKind(v___x_3969_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v_env_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3972_ = lean_st_ref_get(v_a_2302_);
v_env_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc_ref(v_env_3973_);
lean_dec(v___x_3972_);
lean_inc_n(v_stx_2296_, 2);
v___x_3974_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_3975_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3976_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3975_, v_env_3973_, v___x_3974_);
v___x_3977_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3978_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_3976_, v___x_3977_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
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
v___x_3993_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
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
v___x_4001_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4000_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4001_;
}
}
else
{
lean_object* v_val_4003_; lean_object* v___x_4005_; 
lean_del_object(v___x_3985_);
lean_dec(v___x_3974_);
lean_dec(v_stx_2296_);
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
lean_dec(v_stx_2296_);
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
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4018_ = lean_unsigned_to_nat(1u);
v___x_4019_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_4018_);
v___x_4020_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
lean_inc(v___x_4019_);
v___x_4021_ = l_Lean_Syntax_isOfKind(v___x_4019_, v___x_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; lean_object* v_env_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
lean_dec(v___x_4019_);
v___x_4022_ = lean_st_ref_get(v_a_2302_);
v_env_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_ref(v_env_4023_);
lean_dec(v___x_4022_);
lean_inc_n(v_stx_2296_, 2);
v___x_4024_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4025_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4026_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4025_, v_env_4023_, v___x_4024_);
v___x_4027_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4028_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4026_, v___x_4027_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_4026_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4059_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v_fst_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4057_; 
v_fst_4033_ = lean_ctor_get(v_a_4029_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v_a_4029_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; 
v_unused_4058_ = lean_ctor_get(v_a_4029_, 1);
lean_dec(v_unused_4058_);
v___x_4035_ = v_a_4029_;
v_isShared_4036_ = v_isSharedCheck_4057_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_fst_4033_);
lean_dec(v_a_4029_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4057_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
if (lean_obj_tag(v_fst_4033_) == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
lean_del_object(v___x_4031_);
v___x_4037_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4038_ = l_Lean_MessageData_ofName(v___x_4024_);
lean_inc_ref(v___x_4038_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set_tag(v___x_4035_, 7);
lean_ctor_set(v___x_4035_, 1, v___x_4038_);
lean_ctor_set(v___x_4035_, 0, v___x_4037_);
v___x_4040_ = v___x_4035_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4041_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_4044_ = l_Lean_indentD(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4042_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4045_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
lean_ctor_set(v___x_4048_, 1, v___x_4038_);
v___x_4049_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___x_4051_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4050_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4051_;
}
}
else
{
lean_object* v_val_4053_; lean_object* v___x_4055_; 
lean_del_object(v___x_4035_);
lean_dec(v___x_4024_);
lean_dec(v_stx_2296_);
v_val_4053_ = lean_ctor_get(v_fst_4033_, 0);
lean_inc(v_val_4053_);
lean_dec_ref(v_fst_4033_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v_val_4053_);
v___x_4055_ = v___x_4031_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_val_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v___x_4024_);
lean_dec(v_stx_2296_);
v_a_4060_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4028_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4028_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_object* v___x_4068_; uint8_t v___x_4069_; 
v___x_4068_ = l_Lean_Syntax_getArg(v___x_4019_, v___x_3968_);
lean_dec(v___x_4019_);
lean_inc(v___x_4068_);
v___x_4069_ = l_Lean_Syntax_matchesNull(v___x_4068_, v___x_4018_);
if (v___x_4069_ == 0)
{
lean_object* v___x_4070_; lean_object* v_env_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec(v___x_4068_);
v___x_4070_ = lean_st_ref_get(v_a_2302_);
v_env_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc_ref(v_env_4071_);
lean_dec(v___x_4070_);
lean_inc_n(v_stx_2296_, 2);
v___x_4072_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4073_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4074_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4073_, v_env_4071_, v___x_4072_);
v___x_4075_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4076_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4074_, v___x_4075_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_4074_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4107_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4107_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4107_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v_fst_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4105_; 
v_fst_4081_ = lean_ctor_get(v_a_4077_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_a_4077_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v_a_4077_, 1);
lean_dec(v_unused_4106_);
v___x_4083_ = v_a_4077_;
v_isShared_4084_ = v_isSharedCheck_4105_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_fst_4081_);
lean_dec(v_a_4077_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4105_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
if (lean_obj_tag(v_fst_4081_) == 0)
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
lean_del_object(v___x_4079_);
v___x_4085_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4086_ = l_Lean_MessageData_ofName(v___x_4072_);
lean_inc_ref(v___x_4086_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 7);
lean_ctor_set(v___x_4083_, 1, v___x_4086_);
lean_ctor_set(v___x_4083_, 0, v___x_4085_);
v___x_4088_ = v___x_4083_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4089_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_4092_ = l_Lean_indentD(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4090_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v___x_4086_);
v___x_4097_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4098_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4099_;
}
}
else
{
lean_object* v_val_4101_; lean_object* v___x_4103_; 
lean_del_object(v___x_4083_);
lean_dec(v___x_4072_);
lean_dec(v_stx_2296_);
v_val_4101_ = lean_ctor_get(v_fst_4081_, 0);
lean_inc(v_val_4101_);
lean_dec_ref(v_fst_4081_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v_val_4101_);
v___x_4103_ = v___x_4079_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_val_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v___x_4072_);
lean_dec(v_stx_2296_);
v_a_4108_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4076_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4076_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
v___x_4116_ = l_Lean_Syntax_getArg(v___x_4068_, v___x_3968_);
lean_dec(v___x_4068_);
v___x_4117_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4118_ = l_Lean_Syntax_isOfKind(v___x_4116_, v___x_4117_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; lean_object* v_env_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4119_ = lean_st_ref_get(v_a_2302_);
v_env_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc_ref(v_env_4120_);
lean_dec(v___x_4119_);
lean_inc_n(v_stx_2296_, 2);
v___x_4121_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4122_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4123_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4122_, v_env_4120_, v___x_4121_);
v___x_4124_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4125_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4123_, v___x_4124_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_4123_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4156_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4156_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4156_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_fst_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4154_; 
v_fst_4130_ = lean_ctor_get(v_a_4126_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_a_4126_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v_a_4126_, 1);
lean_dec(v_unused_4155_);
v___x_4132_ = v_a_4126_;
v_isShared_4133_ = v_isSharedCheck_4154_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_fst_4130_);
lean_dec(v_a_4126_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4154_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
if (lean_obj_tag(v_fst_4130_) == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
lean_del_object(v___x_4128_);
v___x_4134_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4135_ = l_Lean_MessageData_ofName(v___x_4121_);
lean_inc_ref(v___x_4135_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 7);
lean_ctor_set(v___x_4132_, 1, v___x_4135_);
lean_ctor_set(v___x_4132_, 0, v___x_4134_);
v___x_4137_ = v___x_4132_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4138_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4137_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_4141_ = l_Lean_indentD(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4139_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
lean_ctor_set(v___x_4145_, 1, v___x_4135_);
v___x_4146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4147_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4148_;
}
}
else
{
lean_object* v_val_4150_; lean_object* v___x_4152_; 
lean_del_object(v___x_4132_);
lean_dec(v___x_4121_);
lean_dec(v_stx_2296_);
v_val_4150_ = lean_ctor_get(v_fst_4130_, 0);
lean_inc(v_val_4150_);
lean_dec_ref(v_fst_4130_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v_val_4150_);
v___x_4152_ = v___x_4128_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_val_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v___x_4121_);
lean_dec(v_stx_2296_);
v_a_4157_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4125_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4125_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
else
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec(v_stx_2296_);
v___x_4165_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
return v___x_4166_;
}
}
}
}
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_4167_);
v___x_4169_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4170_ = l_Lean_Syntax_isOfKind(v___x_4168_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v_env_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4171_ = lean_st_ref_get(v_a_2302_);
v_env_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc_ref(v_env_4172_);
lean_dec(v___x_4171_);
lean_inc_n(v_stx_2296_, 2);
v___x_4173_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4174_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4175_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4174_, v_env_4172_, v___x_4173_);
v___x_4176_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4177_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4175_, v___x_4176_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
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
v___x_4192_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
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
v___x_4200_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4199_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4200_;
}
}
else
{
lean_object* v_val_4202_; lean_object* v___x_4204_; 
lean_del_object(v___x_4184_);
lean_dec(v___x_4173_);
lean_dec(v_stx_2296_);
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
lean_dec(v_stx_2296_);
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
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4217_ = lean_unsigned_to_nat(2u);
v___x_4218_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_4217_);
v___x_4219_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4220_ = l_Lean_Syntax_isOfKind(v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v_env_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4221_ = lean_st_ref_get(v_a_2302_);
v_env_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc_ref(v_env_4222_);
lean_dec(v___x_4221_);
lean_inc_n(v_stx_2296_, 2);
v___x_4223_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4224_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4225_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4224_, v_env_4222_, v___x_4223_);
v___x_4226_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4227_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4225_, v___x_4226_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_4225_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4258_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4258_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4258_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v_fst_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4256_; 
v_fst_4232_ = lean_ctor_get(v_a_4228_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_a_4228_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; 
v_unused_4257_ = lean_ctor_get(v_a_4228_, 1);
lean_dec(v_unused_4257_);
v___x_4234_ = v_a_4228_;
v_isShared_4235_ = v_isSharedCheck_4256_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_fst_4232_);
lean_dec(v_a_4228_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4256_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
if (lean_obj_tag(v_fst_4232_) == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
lean_del_object(v___x_4230_);
v___x_4236_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4237_ = l_Lean_MessageData_ofName(v___x_4223_);
lean_inc_ref(v___x_4237_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set_tag(v___x_4234_, 7);
lean_ctor_set(v___x_4234_, 1, v___x_4237_);
lean_ctor_set(v___x_4234_, 0, v___x_4236_);
v___x_4239_ = v___x_4234_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4236_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4240_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4239_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_4243_ = l_Lean_indentD(v___x_4242_);
v___x_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4241_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
lean_ctor_set(v___x_4247_, 1, v___x_4237_);
v___x_4248_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4247_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4249_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4250_;
}
}
else
{
lean_object* v_val_4252_; lean_object* v___x_4254_; 
lean_del_object(v___x_4234_);
lean_dec(v___x_4223_);
lean_dec(v_stx_2296_);
v_val_4252_ = lean_ctor_get(v_fst_4232_, 0);
lean_inc(v_val_4252_);
lean_dec_ref(v_fst_4232_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 0, v_val_4252_);
v___x_4254_ = v___x_4230_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_val_4252_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec(v___x_4223_);
lean_dec(v_stx_2296_);
v_a_4259_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4227_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4227_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_dec(v_stx_2296_);
v___x_4267_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
return v___x_4268_;
}
}
}
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v___x_4269_ = lean_unsigned_to_nat(1u);
v___x_4270_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_4269_);
v___x_4271_ = l_Lean_Syntax_isNone(v___x_4270_);
if (v___x_4271_ == 0)
{
uint8_t v___x_4272_; 
v___x_4272_ = l_Lean_Syntax_matchesNull(v___x_4270_, v___x_4269_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v_env_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_del_object(v___x_2333_);
v___x_4273_ = lean_st_ref_get(v_a_2302_);
v_env_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc_ref(v_env_4274_);
lean_dec(v___x_4273_);
lean_inc_n(v_stx_2296_, 2);
v___x_4275_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4276_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4277_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4276_, v_env_4274_, v___x_4275_);
v___x_4278_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4279_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4277_, v___x_4278_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_4277_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4310_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4310_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4310_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_fst_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4308_; 
v_fst_4284_ = lean_ctor_get(v_a_4280_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_a_4280_);
if (v_isSharedCheck_4308_ == 0)
{
lean_object* v_unused_4309_; 
v_unused_4309_ = lean_ctor_get(v_a_4280_, 1);
lean_dec(v_unused_4309_);
v___x_4286_ = v_a_4280_;
v_isShared_4287_ = v_isSharedCheck_4308_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_fst_4284_);
lean_dec(v_a_4280_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4308_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
if (lean_obj_tag(v_fst_4284_) == 0)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4291_; 
lean_del_object(v___x_4282_);
v___x_4288_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4289_ = l_Lean_MessageData_ofName(v___x_4275_);
lean_inc_ref(v___x_4289_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set_tag(v___x_4286_, 7);
lean_ctor_set(v___x_4286_, 1, v___x_4289_);
lean_ctor_set(v___x_4286_, 0, v___x_4288_);
v___x_4291_ = v___x_4286_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4288_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v___x_4289_);
v___x_4291_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4292_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_4295_ = l_Lean_indentD(v___x_4294_);
v___x_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4293_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
lean_ctor_set(v___x_4299_, 1, v___x_4289_);
v___x_4300_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4301_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4302_;
}
}
else
{
lean_object* v_val_4304_; lean_object* v___x_4306_; 
lean_del_object(v___x_4286_);
lean_dec(v___x_4275_);
lean_dec(v_stx_2296_);
v_val_4304_ = lean_ctor_get(v_fst_4284_, 0);
lean_inc(v_val_4304_);
lean_dec_ref(v_fst_4284_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v_val_4304_);
v___x_4306_ = v___x_4282_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_val_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_dec(v___x_4275_);
lean_dec(v_stx_2296_);
v_a_4311_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4279_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4279_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
else
{
v___y_2421_ = v_a_2297_;
v___y_2422_ = v_a_2298_;
v___y_2423_ = v_a_2299_;
v___y_2424_ = v_a_2300_;
v___y_2425_ = v_a_2301_;
v___y_2426_ = v_a_2302_;
goto v___jp_2420_;
}
}
else
{
lean_dec(v___x_4270_);
v___y_2421_ = v_a_2297_;
v___y_2422_ = v_a_2298_;
v___y_2423_ = v_a_2299_;
v___y_2424_ = v_a_2300_;
v___y_2425_ = v_a_2301_;
v___y_2426_ = v_a_2302_;
goto v___jp_2420_;
}
}
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_del_object(v___x_2333_);
v___x_4319_ = lean_unsigned_to_nat(1u);
v___x_4320_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_4319_);
lean_dec(v_stx_2296_);
v___x_4321_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4320_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4321_;
}
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
lean_del_object(v___x_2333_);
lean_dec(v_stx_2296_);
v___x_4322_ = lean_unsigned_to_nat(1u);
v___x_4323_ = l_Lean_NameSet_empty;
v___x_4324_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
lean_ctor_set_uint8(v___x_4324_, sizeof(void*)*2, v___x_2537_);
lean_ctor_set_uint8(v___x_4324_, sizeof(void*)*2 + 1, v___x_2537_);
lean_ctor_set_uint8(v___x_4324_, sizeof(void*)*2 + 2, v___x_2537_);
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
lean_del_object(v___x_2333_);
v___x_4326_ = lean_unsigned_to_nat(0u);
v___x_4331_ = lean_unsigned_to_nat(1u);
v___x_4332_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_4331_);
v___x_4333_ = l_Lean_Syntax_isNone(v___x_4332_);
if (v___x_4333_ == 0)
{
uint8_t v___x_4334_; 
v___x_4334_ = l_Lean_Syntax_matchesNull(v___x_4332_, v___x_4331_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; lean_object* v_env_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4335_ = lean_st_ref_get(v_a_2302_);
v_env_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc_ref(v_env_4336_);
lean_dec(v___x_4335_);
lean_inc_n(v_stx_2296_, 2);
v___x_4337_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_4338_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4339_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4338_, v_env_4336_, v___x_4337_);
v___x_4340_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4341_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_4339_, v___x_4340_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v___x_4339_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4372_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4344_ = v___x_4341_;
v_isShared_4345_ = v_isSharedCheck_4372_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4341_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4372_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_fst_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4370_; 
v_fst_4346_ = lean_ctor_get(v_a_4342_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v_a_4342_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v_a_4342_, 1);
lean_dec(v_unused_4371_);
v___x_4348_ = v_a_4342_;
v_isShared_4349_ = v_isSharedCheck_4370_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_fst_4346_);
lean_dec(v_a_4342_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4370_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
if (lean_obj_tag(v_fst_4346_) == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4353_; 
lean_del_object(v___x_4344_);
v___x_4350_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4351_ = l_Lean_MessageData_ofName(v___x_4337_);
lean_inc_ref(v___x_4351_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 7);
lean_ctor_set(v___x_4348_, 1, v___x_4351_);
lean_ctor_set(v___x_4348_, 0, v___x_4350_);
v___x_4353_ = v___x_4348_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4350_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4354_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4353_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_4357_ = l_Lean_indentD(v___x_4356_);
v___x_4358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4355_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
v___x_4361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
lean_ctor_set(v___x_4361_, 1, v___x_4351_);
v___x_4362_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4361_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
v___x_4364_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4363_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_4364_;
}
}
else
{
lean_object* v_val_4366_; lean_object* v___x_4368_; 
lean_del_object(v___x_4348_);
lean_dec(v___x_4337_);
lean_dec(v_stx_2296_);
v_val_4366_ = lean_ctor_get(v_fst_4346_, 0);
lean_inc(v_val_4366_);
lean_dec_ref(v_fst_4346_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v_val_4366_);
v___x_4368_ = v___x_4344_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_val_4366_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v___x_4337_);
lean_dec(v_stx_2296_);
v_a_4373_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4341_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4341_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_dec(v_stx_2296_);
goto v___jp_4327_;
}
}
else
{
lean_dec(v___x_4332_);
lean_dec(v_stx_2296_);
goto v___jp_4327_;
}
v___jp_4327_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = l_Lean_NameSet_empty;
v___x_4329_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4329_, 0, v___x_4326_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
lean_ctor_set_uint8(v___x_4329_, sizeof(void*)*2, v___x_2535_);
lean_ctor_set_uint8(v___x_4329_, sizeof(void*)*2 + 1, v___x_2535_);
lean_ctor_set_uint8(v___x_4329_, sizeof(void*)*2 + 2, v___x_2533_);
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
return v___x_4330_;
}
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_del_object(v___x_2333_);
lean_dec(v_stx_2296_);
v___x_4381_ = lean_unsigned_to_nat(0u);
v___x_4382_ = l_Lean_NameSet_empty;
v___x_4383_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4383_, 0, v___x_4381_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2, v___x_2532_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2 + 1, v___x_2533_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2 + 2, v___x_2532_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_del_object(v___x_2333_);
lean_dec(v_stx_2296_);
v___x_4385_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
v___jp_2349_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2356_ = lean_unsigned_to_nat(2u);
v___x_2357_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2356_);
v___x_2358_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2359_ = l_Lean_Syntax_isOfKind(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v_env_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2360_ = lean_st_ref_get(v___y_2355_);
v_env_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc_ref(v_env_2361_);
lean_dec(v___x_2360_);
lean_inc_n(v_stx_2296_, 2);
v___x_2362_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2363_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2364_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2363_, v_env_2361_, v___x_2362_);
v___x_2365_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2366_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2364_, v___x_2365_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___x_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2397_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2397_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2397_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_fst_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2395_; 
v_fst_2371_ = lean_ctor_get(v_a_2367_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_a_2367_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v_a_2367_, 1);
lean_dec(v_unused_2396_);
v___x_2373_ = v_a_2367_;
v_isShared_2374_ = v_isSharedCheck_2395_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_fst_2371_);
lean_dec(v_a_2367_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2395_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
if (lean_obj_tag(v_fst_2371_) == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_del_object(v___x_2369_);
v___x_2375_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2376_ = l_Lean_MessageData_ofName(v___x_2362_);
lean_inc_ref(v___x_2376_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set_tag(v___x_2373_, 7);
lean_ctor_set(v___x_2373_, 1, v___x_2376_);
lean_ctor_set(v___x_2373_, 0, v___x_2375_);
v___x_2378_ = v___x_2373_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2379_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2382_ = l_Lean_indentD(v___x_2381_);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2380_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___x_2376_);
v___x_2387_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2388_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
return v___x_2389_;
}
}
else
{
lean_object* v_val_2391_; lean_object* v___x_2393_; 
lean_del_object(v___x_2373_);
lean_dec(v___x_2362_);
lean_dec(v_stx_2296_);
v_val_2391_ = lean_ctor_get(v_fst_2371_, 0);
lean_inc(v_val_2391_);
lean_dec_ref(v_fst_2371_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v_val_2391_);
v___x_2393_ = v___x_2369_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_val_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v___x_2362_);
lean_dec(v_stx_2296_);
v_a_2398_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2366_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2366_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2406_ = lean_unsigned_to_nat(7u);
v___x_2407_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2406_);
v___x_2408_ = lean_unsigned_to_nat(8u);
v___x_2409_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2408_);
lean_dec(v_stx_2296_);
v___x_2410_ = l_Lean_Syntax_getOptional_x3f(v___x_2409_);
lean_dec(v___x_2409_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_box(0);
v___y_2305_ = v___y_2354_;
v___y_2306_ = v___x_2407_;
v___y_2307_ = v___y_2350_;
v___y_2308_ = v___y_2351_;
v___y_2309_ = v___y_2355_;
v___y_2310_ = v___y_2353_;
v___y_2311_ = v___y_2352_;
v___y_2312_ = v___x_2411_;
goto v___jp_2304_;
}
else
{
lean_object* v_val_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_val_2412_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2410_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_val_2412_);
lean_dec(v___x_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_val_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
v___y_2305_ = v___y_2354_;
v___y_2306_ = v___x_2407_;
v___y_2307_ = v___y_2350_;
v___y_2308_ = v___y_2351_;
v___y_2309_ = v___y_2355_;
v___y_2310_ = v___y_2353_;
v___y_2311_ = v___y_2352_;
v___y_2312_ = v___x_2417_;
goto v___jp_2304_;
}
}
}
}
}
v___jp_2420_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2427_ = lean_unsigned_to_nat(2u);
v___x_2428_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2430_ = l_Lean_Syntax_isOfKind(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v_env_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_del_object(v___x_2333_);
v___x_2431_ = lean_st_ref_get(v___y_2426_);
v_env_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc_ref(v_env_2432_);
lean_dec(v___x_2431_);
lean_inc_n(v_stx_2296_, 2);
v___x_2433_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2434_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2435_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2434_, v_env_2432_, v___x_2433_);
v___x_2436_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2437_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2435_, v___x_2436_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___x_2435_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2468_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2468_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2468_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_fst_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2466_; 
v_fst_2442_ = lean_ctor_get(v_a_2438_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v_a_2438_, 1);
lean_dec(v_unused_2467_);
v___x_2444_ = v_a_2438_;
v_isShared_2445_ = v_isSharedCheck_2466_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_fst_2442_);
lean_dec(v_a_2438_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2466_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
if (lean_obj_tag(v_fst_2442_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_del_object(v___x_2440_);
v___x_2446_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2447_ = l_Lean_MessageData_ofName(v___x_2433_);
lean_inc_ref(v___x_2447_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set_tag(v___x_2444_, 7);
lean_ctor_set(v___x_2444_, 1, v___x_2447_);
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2450_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2453_ = l_Lean_indentD(v___x_2452_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2451_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2447_);
v___x_2458_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2459_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2460_;
}
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; 
lean_del_object(v___x_2444_);
lean_dec(v___x_2433_);
lean_dec(v_stx_2296_);
v_val_2462_ = lean_ctor_get(v_fst_2442_, 0);
lean_inc(v_val_2462_);
lean_dec_ref(v_fst_2442_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_val_2462_);
v___x_2464_ = v___x_2440_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_val_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v___x_2433_);
lean_dec(v_stx_2296_);
v_a_2469_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2437_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2437_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2477_ = lean_unsigned_to_nat(3u);
v___x_2478_ = l_Lean_Syntax_getArg(v_stx_2296_, v___x_2477_);
v___x_2479_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2480_ = l_Lean_Syntax_isOfKind(v___x_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v_env_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_del_object(v___x_2333_);
v___x_2481_ = lean_st_ref_get(v___y_2426_);
v_env_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_env_2482_);
lean_dec(v___x_2481_);
lean_inc_n(v_stx_2296_, 2);
v___x_2483_ = l_Lean_Syntax_getKind(v_stx_2296_);
v___x_2484_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2485_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2484_, v_env_2482_, v___x_2483_);
v___x_2486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2487_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2296_, v___x_2485_, v___x_2486_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___x_2485_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2518_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2518_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2518_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_fst_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2516_; 
v_fst_2492_ = lean_ctor_get(v_a_2488_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_a_2488_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v_a_2488_, 1);
lean_dec(v_unused_2517_);
v___x_2494_ = v_a_2488_;
v_isShared_2495_ = v_isSharedCheck_2516_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_fst_2492_);
lean_dec(v_a_2488_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2516_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
if (lean_obj_tag(v_fst_2492_) == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_del_object(v___x_2490_);
v___x_2496_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2497_ = l_Lean_MessageData_ofName(v___x_2483_);
lean_inc_ref(v___x_2497_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 7);
lean_ctor_set(v___x_2494_, 1, v___x_2497_);
lean_ctor_set(v___x_2494_, 0, v___x_2496_);
v___x_2499_ = v___x_2494_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_MessageData_ofSyntax(v_stx_2296_);
v___x_2503_ = l_Lean_indentD(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2501_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2497_);
v___x_2508_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2509_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2510_;
}
}
else
{
lean_object* v_val_2512_; lean_object* v___x_2514_; 
lean_del_object(v___x_2494_);
lean_dec(v___x_2483_);
lean_dec(v_stx_2296_);
v_val_2512_ = lean_ctor_get(v_fst_2492_, 0);
lean_inc(v_val_2512_);
lean_dec_ref(v_fst_2492_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v_val_2512_);
v___x_2514_ = v___x_2490_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_val_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v___x_2483_);
lean_dec(v_stx_2296_);
v_a_2519_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2487_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2487_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_dec(v_stx_2296_);
v___x_2527_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2527_);
v___x_2529_ = v___x_2333_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
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
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_stx_2296_);
v_a_4388_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_2330_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_2330_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
v___jp_2304_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2313_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___y_2306_);
v___x_2316_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2313_, v___x_2314_, v___x_2315_, v___y_2312_, v___y_2307_, v___y_2308_, v___y_2311_, v___y_2310_, v___y_2305_, v___y_2309_);
return v___x_2316_;
}
v___jp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2318_, v_bodyInfo_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
v___jp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2323_, v_bodyInfo_2324_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4396_, size_t v_sz_4397_, size_t v_i_4398_, lean_object* v_b_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
uint8_t v___x_4407_; 
v___x_4407_ = lean_usize_dec_lt(v_i_4398_, v_sz_4397_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
v___x_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4408_, 0, v_b_4399_);
return v___x_4408_;
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4410_; 
v_a_4409_ = lean_array_uget_borrowed(v_as_4396_, v_i_4398_);
lean_inc(v_a_4409_);
v___x_4410_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4409_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; size_t v___x_4413_; size_t v___x_4414_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
v___x_4412_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_4399_, v_a_4411_);
v___x_4413_ = ((size_t)1ULL);
v___x_4414_ = lean_usize_add(v_i_4398_, v___x_4413_);
v_i_4398_ = v___x_4414_;
v_b_4399_ = v___x_4412_;
goto _start;
}
else
{
lean_dec_ref(v_b_4399_);
return v___x_4410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v_info_4424_; lean_object* v___x_4425_; size_t v_sz_4426_; size_t v___x_4427_; lean_object* v___x_4428_; 
v_info_4424_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4425_ = l_Lean_Parser_Term_getDoElems(v_stx_4416_);
v_sz_4426_ = lean_array_size(v___x_4425_);
v___x_4427_ = ((size_t)0ULL);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4425_, v_sz_4426_, v___x_4427_, v_info_4424_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_);
lean_dec_ref(v___x_4425_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
lean_dec(v_a_4433_);
lean_dec_ref(v_a_4432_);
lean_dec(v_a_4431_);
lean_dec_ref(v_a_4430_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4447_, lean_object* v_sz_4448_, lean_object* v_i_4449_, lean_object* v_b_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
size_t v_sz_boxed_4458_; size_t v_i_boxed_4459_; lean_object* v_res_4460_; 
v_sz_boxed_4458_ = lean_unbox_usize(v_sz_4448_);
lean_dec(v_sz_4448_);
v_i_boxed_4459_ = lean_unbox_usize(v_i_4449_);
lean_dec(v_i_4449_);
v_res_4460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4447_, v_sz_boxed_4458_, v_i_boxed_4459_, v_b_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v_as_4447_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4461_, lean_object* v_sz_4462_, lean_object* v_i_4463_, lean_object* v_b_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
size_t v_sz_boxed_4472_; size_t v_i_boxed_4473_; lean_object* v_res_4474_; 
v_sz_boxed_4472_ = lean_unbox_usize(v_sz_4462_);
lean_dec(v_sz_4462_);
v_i_boxed_4473_ = lean_unbox_usize(v_i_4463_);
lean_dec(v_i_4463_);
v_res_4474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4461_, v_sz_boxed_4472_, v_i_boxed_4473_, v_b_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v_as_4461_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4475_, lean_object* v_rhs_x3f_4476_, lean_object* v_otherwise_x3f_4477_, lean_object* v_body_x3f_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4475_, v_rhs_x3f_4476_, v_otherwise_x3f_4477_, v_body_x3f_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
lean_dec(v_a_4480_);
lean_dec_ref(v_a_4479_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4487_, lean_object* v_as_4488_, lean_object* v_sz_4489_, lean_object* v_i_4490_, lean_object* v_b_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
uint8_t v___x_288817__boxed_4499_; size_t v_sz_boxed_4500_; size_t v_i_boxed_4501_; lean_object* v_res_4502_; 
v___x_288817__boxed_4499_ = lean_unbox(v___x_4487_);
v_sz_boxed_4500_ = lean_unbox_usize(v_sz_4489_);
lean_dec(v_sz_4489_);
v_i_boxed_4501_ = lean_unbox_usize(v_i_4490_);
lean_dec(v_i_4490_);
v_res_4502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_288817__boxed_4499_, v_as_4488_, v_sz_boxed_4500_, v_i_boxed_4501_, v_b_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec_ref(v_as_4488_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4503_, lean_object* v_as_4504_, lean_object* v_sz_4505_, lean_object* v_i_4506_, lean_object* v_b_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
uint8_t v___x_288868__boxed_4515_; size_t v_sz_boxed_4516_; size_t v_i_boxed_4517_; lean_object* v_res_4518_; 
v___x_288868__boxed_4515_ = lean_unbox(v___x_4503_);
v_sz_boxed_4516_ = lean_unbox_usize(v_sz_4505_);
lean_dec(v_sz_4505_);
v_i_boxed_4517_ = lean_unbox_usize(v_i_4506_);
lean_dec(v_i_4506_);
v_res_4518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_288868__boxed_4515_, v_as_4504_, v_sz_boxed_4516_, v_i_boxed_4517_, v_b_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec_ref(v_as_4504_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4519_, lean_object* v_sz_4520_, lean_object* v_i_4521_, lean_object* v_b_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
size_t v_sz_boxed_4530_; size_t v_i_boxed_4531_; lean_object* v_res_4532_; 
v_sz_boxed_4530_ = lean_unbox_usize(v_sz_4520_);
lean_dec(v_sz_4520_);
v_i_boxed_4531_ = lean_unbox_usize(v_i_4521_);
lean_dec(v_i_4521_);
v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4519_, v_sz_boxed_4530_, v_i_boxed_4531_, v_b_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec_ref(v_as_4519_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4533_, lean_object* v_decl_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
uint8_t v_reassignment_boxed_4542_; lean_object* v_res_4543_; 
v_reassignment_boxed_4542_ = lean_unbox(v_reassignment_4533_);
v_res_4543_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4542_, v_decl_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4571_, lean_object* v_ref_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v___x_4580_; 
v___x_4580_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4572_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4581_, lean_object* v_ref_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4581_, v_ref_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4591_, lean_object* v_x_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v___x_4600_; 
v___x_4600_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4601_, lean_object* v_x_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4601_, v_x_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4611_, lean_object* v_as_4612_, lean_object* v_as_x27_4613_, lean_object* v_b_4614_, lean_object* v_a_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4611_, v_as_x27_4613_, v_b_4614_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4624_, lean_object* v_as_4625_, lean_object* v_as_x27_4626_, lean_object* v_b_4627_, lean_object* v_a_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4624_, v_as_4625_, v_as_x27_4626_, v_b_4627_, v_a_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v_as_x27_4626_);
lean_dec(v_as_4625_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4637_, lean_object* v_msg_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4647_, lean_object* v_msg_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4647_, v_msg_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4657_, lean_object* v_msg_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4657_, v_msg_4658_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4667_, lean_object* v_msg_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4667_, v_msg_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4677_, lean_object* v_as_x27_4678_, lean_object* v_b_4679_, lean_object* v_a_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4678_, v_b_4679_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4689_, lean_object* v_as_x27_4690_, lean_object* v_b_4691_, lean_object* v_a_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4689_, v_as_x27_4690_, v_b_4691_, v_a_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v_as_x27_4690_);
lean_dec(v_as_4689_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4701_, lean_object* v_ref_4702_, lean_object* v_msg_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4702_, v_msg_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4712_, lean_object* v_ref_4713_, lean_object* v_msg_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4712_, v_ref_4713_, v_msg_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v_ref_4713_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4723_, lean_object* v_macroStack_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4723_, v_macroStack_4724_, v___y_4729_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4733_, lean_object* v_macroStack_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4733_, v_macroStack_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4743_, lean_object* v_m_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4744_, v_a_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4747_, lean_object* v_m_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4747_, v_m_4748_, v_a_4749_);
lean_dec(v_a_4749_);
lean_dec_ref(v_m_4748_);
return v_res_4750_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4751_, lean_object* v_x_4752_, lean_object* v_x_4753_){
_start:
{
uint8_t v___x_4754_; 
v___x_4754_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4752_, v_x_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4755_, lean_object* v_x_4756_, lean_object* v_x_4757_){
_start:
{
uint8_t v_res_4758_; lean_object* v_r_4759_; 
v_res_4758_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4755_, v_x_4756_, v_x_4757_);
lean_dec_ref(v_x_4757_);
lean_dec_ref(v_x_4756_);
v_r_4759_ = lean_box(v_res_4758_);
return v_r_4759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4760_, lean_object* v_a_4761_, lean_object* v_x_4762_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4761_, v_x_4762_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4764_, lean_object* v_a_4765_, lean_object* v_x_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4764_, v_a_4765_, v_x_4766_);
lean_dec(v_x_4766_);
lean_dec(v_a_4765_);
return v_res_4767_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4768_, lean_object* v_x_4769_, size_t v_x_4770_, lean_object* v_x_4771_){
_start:
{
uint8_t v___x_4772_; 
v___x_4772_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4769_, v_x_4770_, v_x_4771_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4773_, lean_object* v_x_4774_, lean_object* v_x_4775_, lean_object* v_x_4776_){
_start:
{
size_t v_x_294585__boxed_4777_; uint8_t v_res_4778_; lean_object* v_r_4779_; 
v_x_294585__boxed_4777_ = lean_unbox_usize(v_x_4775_);
lean_dec(v_x_4775_);
v_res_4778_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4773_, v_x_4774_, v_x_294585__boxed_4777_, v_x_4776_);
lean_dec_ref(v_x_4776_);
lean_dec_ref(v_x_4774_);
v_r_4779_ = lean_box(v_res_4778_);
return v_r_4779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4780_, lean_object* v_keys_4781_, lean_object* v_vals_4782_, lean_object* v_heq_4783_, lean_object* v_i_4784_, lean_object* v_k_4785_){
_start:
{
uint8_t v___x_4786_; 
v___x_4786_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4781_, v_i_4784_, v_k_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4787_, lean_object* v_keys_4788_, lean_object* v_vals_4789_, lean_object* v_heq_4790_, lean_object* v_i_4791_, lean_object* v_k_4792_){
_start:
{
uint8_t v_res_4793_; lean_object* v_r_4794_; 
v_res_4793_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4787_, v_keys_4788_, v_vals_4789_, v_heq_4790_, v_i_4791_, v_k_4792_);
lean_dec_ref(v_k_4792_);
lean_dec_ref(v_vals_4789_);
lean_dec_ref(v_keys_4788_);
v_r_4794_ = lean_box(v_res_4793_);
return v_r_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v___x_4803_; 
v___x_4803_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
return v_res_4830_;
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
