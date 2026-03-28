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
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
lean_inc_ref(v___y_124_);
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
lean_inc_ref(v___y_145_);
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
lean_inc_ref(v___y_155_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v_env_260_; lean_object* v___x_261_; lean_object* v_mctx_262_; lean_object* v_lctx_263_; lean_object* v_options_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v___x_261_ = lean_st_ref_get(v___y_255_);
v_mctx_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc_ref(v_mctx_262_);
lean_dec(v___x_261_);
v_lctx_263_ = lean_ctor_get(v___y_254_, 2);
v_options_264_ = lean_ctor_get(v___y_256_, 2);
lean_inc_ref(v_options_264_);
lean_inc_ref(v_lctx_263_);
v___x_265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_265_, 0, v_env_260_);
lean_ctor_set(v___x_265_, 1, v_mctx_262_);
lean_ctor_set(v___x_265_, 2, v_lctx_263_);
lean_ctor_set(v___x_265_, 3, v_options_264_);
v___x_266_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_msgData_253_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_274_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(1);
v___x_276_ = l_Lean_MessageData_ofFormat(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_281_ = l_Lean_MessageData_ofFormat(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
return v_x_282_;
}
else
{
lean_object* v_head_284_; lean_object* v_tail_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_307_; 
v_head_284_ = lean_ctor_get(v_x_283_, 0);
v_tail_285_ = lean_ctor_get(v_x_283_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_307_ == 0)
{
v___x_287_ = v_x_283_;
v_isShared_288_ = v_isSharedCheck_307_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_tail_285_);
lean_inc(v_head_284_);
lean_dec(v_x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_307_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_before_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_305_; 
v_before_289_ = lean_ctor_get(v_head_284_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_head_284_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_head_284_, 1);
lean_dec(v_unused_306_);
v___x_291_ = v_head_284_;
v_isShared_292_ = v_isSharedCheck_305_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_before_289_);
lean_dec(v_head_284_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_305_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 7);
lean_ctor_set(v___x_291_, 1, v___x_293_);
lean_ctor_set(v___x_291_, 0, v_x_282_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_x_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_304_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 7);
lean_ctor_set(v___x_287_, 1, v___x_296_);
lean_ctor_set(v___x_287_, 0, v___x_295_);
v___x_298_ = v___x_287_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_MessageData_ofSyntax(v_before_289_);
v___x_300_ = l_Lean_indentD(v___x_299_);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v_x_282_ = v___x_301_;
v_x_283_ = v_tail_285_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_308_, lean_object* v_opt_309_){
_start:
{
lean_object* v_name_310_; lean_object* v_defValue_311_; lean_object* v_map_312_; lean_object* v___x_313_; 
v_name_310_ = lean_ctor_get(v_opt_309_, 0);
v_defValue_311_ = lean_ctor_get(v_opt_309_, 1);
v_map_312_ = lean_ctor_get(v_opts_308_, 0);
v___x_313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_312_, v_name_310_);
if (lean_obj_tag(v___x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = lean_unbox(v_defValue_311_);
return v___x_314_;
}
else
{
lean_object* v_val_315_; 
v_val_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_315_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v_val_315_) == 1)
{
uint8_t v_v_316_; 
v_v_316_ = lean_ctor_get_uint8(v_val_315_, 0);
lean_dec_ref(v_val_315_);
return v_v_316_;
}
else
{
uint8_t v___x_317_; 
lean_dec(v_val_315_);
v___x_317_ = lean_unbox(v_defValue_311_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_318_, lean_object* v_opt_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_318_, v_opt_319_);
lean_dec_ref(v_opt_319_);
lean_dec_ref(v_opts_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_327_, lean_object* v_macroStack_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_options_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_options_331_ = lean_ctor_get(v___y_329_, 2);
v___x_332_ = l_Lean_Elab_pp_macroStack;
v___x_333_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_macroStack_328_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_msgData_327_);
return v___x_334_;
}
else
{
if (lean_obj_tag(v_macroStack_328_) == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_msgData_327_);
return v___x_335_;
}
else
{
lean_object* v_head_336_; lean_object* v_after_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_352_; 
v_head_336_ = lean_ctor_get(v_macroStack_328_, 0);
lean_inc(v_head_336_);
v_after_337_ = lean_ctor_get(v_head_336_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_head_336_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_head_336_, 0);
lean_dec(v_unused_353_);
v___x_339_ = v_head_336_;
v_isShared_340_ = v_isSharedCheck_352_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_after_337_);
lean_dec(v_head_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_352_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 7);
lean_ctor_set(v___x_339_, 1, v___x_341_);
lean_ctor_set(v___x_339_, 0, v_msgData_327_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_msgData_327_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_351_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_msgData_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_344_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_MessageData_ofSyntax(v_after_337_);
v___x_347_ = l_Lean_indentD(v___x_346_);
v_msgData_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_348_, 0, v___x_345_);
lean_ctor_set(v_msgData_348_, 1, v___x_347_);
v___x_349_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_348_, v_macroStack_328_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_354_, lean_object* v_macroStack_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_354_, v_macroStack_355_, v___y_356_);
lean_dec_ref(v___y_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_ref_367_; lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v_macroStack_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_ref_367_ = lean_ctor_get(v___y_364_, 5);
v___x_368_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_359_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v_macroStack_370_ = lean_ctor_get(v___y_360_, 1);
lean_inc_n(v_macroStack_370_, 2);
v___x_371_ = l_Lean_Elab_getBetterRef(v_ref_367_, v_macroStack_370_);
v___x_372_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_369_, v_macroStack_370_, v___y_364_);
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
lean_dec_ref(v___y_383_);
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
uint8_t v___x_259312__boxed_494_; uint8_t v___x_259313__boxed_495_; size_t v_i_boxed_496_; size_t v_stop_boxed_497_; lean_object* v_res_498_; 
v___x_259312__boxed_494_ = lean_unbox(v___x_488_);
v___x_259313__boxed_495_ = lean_unbox(v___x_489_);
v_i_boxed_496_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_497_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_259312__boxed_494_, v___x_259313__boxed_495_, v_as_490_, v_i_boxed_496_, v_stop_boxed_497_, v_b_493_);
lean_dec_ref(v_as_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_499_, lean_object* v_declName_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_503_; lean_object* v_env_504_; lean_object* v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_503_ = 0;
v_env_504_ = l_Lean_Environment_setExporting(v_env_499_, v___x_503_);
lean_inc(v_declName_500_);
v___x_505_ = l_Lean_mkPrivateName(v_env_504_, v_declName_500_);
v___x_506_ = 1;
lean_inc_ref(v_env_504_);
v___x_507_ = l_Lean_Environment_contains(v_env_504_, v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = l_Lean_privateToUserName(v_declName_500_);
v___x_509_ = l_Lean_Environment_contains(v_env_504_, v___x_508_, v___x_506_);
v___x_510_ = lean_box(v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___y_502_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v_env_504_);
lean_dec(v_declName_500_);
v___x_512_ = lean_box(v___x_507_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___y_502_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_514_, lean_object* v_declName_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_514_, v_declName_515_, v___y_516_, v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_maxRecDepthErrorMessage;
v___x_525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_527_ = l_Lean_MessageData_ofFormat(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_529_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_530_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_ref_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_539_, lean_object* v___y_540_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_a_541_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_541_);
lean_ctor_set(v___x_542_, 1, v___y_540_);
return v___x_542_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_544_; 
v_a_543_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_a_543_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_543_);
lean_ctor_set(v___x_544_, 1, v___y_540_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_545_, v___y_546_);
lean_dec_ref(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_548_, lean_object* v_stx_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_548_, v_stx_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
if (lean_obj_tag(v_a_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_a_554_ = lean_ctor_get(v___x_552_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_563_);
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_a_554_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_592_; 
v_val_564_ = lean_ctor_get(v_a_553_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_592_ == 0)
{
v___x_566_ = v_a_553_;
v_isShared_567_ = v_isSharedCheck_592_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v_a_553_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_592_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_snd_568_; 
v_snd_568_ = lean_ctor_get(v_val_564_, 1);
lean_inc(v_snd_568_);
lean_dec(v_val_564_);
if (lean_obj_tag(v_snd_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_566_);
v_a_569_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_a_569_);
lean_dec_ref(v___x_552_);
v_a_570_ = lean_ctor_get(v_snd_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_snd_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_snd_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_snd_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_575_, v_a_569_);
lean_dec_ref(v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_591_; 
v_a_579_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_a_579_);
lean_dec_ref(v___x_552_);
v_a_580_ = lean_ctor_get(v_snd_568_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_snd_568_);
if (v_isSharedCheck_591_ == 0)
{
v___x_582_ = v_snd_568_;
v_isShared_583_ = v_isSharedCheck_591_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v_snd_568_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_591_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_a_580_);
v___x_585_ = v___x_566_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_590_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_585_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_587_, v_a_579_);
lean_dec_ref(v___x_587_);
return v___x_588_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_593_ = lean_ctor_get(v___x_552_, 0);
v_a_594_ = lean_ctor_get(v___x_552_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_552_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_inc(v_a_593_);
lean_dec(v___x_552_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_602_, lean_object* v_stx_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_602_, v_stx_603_, v___y_604_, v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_607_, lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_fileName_616_; lean_object* v_fileMap_617_; lean_object* v_options_618_; lean_object* v_currRecDepth_619_; lean_object* v_maxRecDepth_620_; lean_object* v_ref_621_; lean_object* v_currNamespace_622_; lean_object* v_openDecls_623_; lean_object* v_initHeartbeats_624_; lean_object* v_maxHeartbeats_625_; lean_object* v_quotContext_626_; lean_object* v_currMacroScope_627_; uint8_t v_diag_628_; lean_object* v_cancelTk_x3f_629_; uint8_t v_suppressElabErrors_630_; lean_object* v_inheritedTraceOptions_631_; lean_object* v_ref_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_fileName_616_ = lean_ctor_get(v___y_613_, 0);
v_fileMap_617_ = lean_ctor_get(v___y_613_, 1);
v_options_618_ = lean_ctor_get(v___y_613_, 2);
v_currRecDepth_619_ = lean_ctor_get(v___y_613_, 3);
v_maxRecDepth_620_ = lean_ctor_get(v___y_613_, 4);
v_ref_621_ = lean_ctor_get(v___y_613_, 5);
v_currNamespace_622_ = lean_ctor_get(v___y_613_, 6);
v_openDecls_623_ = lean_ctor_get(v___y_613_, 7);
v_initHeartbeats_624_ = lean_ctor_get(v___y_613_, 8);
v_maxHeartbeats_625_ = lean_ctor_get(v___y_613_, 9);
v_quotContext_626_ = lean_ctor_get(v___y_613_, 10);
v_currMacroScope_627_ = lean_ctor_get(v___y_613_, 11);
v_diag_628_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*14);
v_cancelTk_x3f_629_ = lean_ctor_get(v___y_613_, 12);
v_suppressElabErrors_630_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_631_ = lean_ctor_get(v___y_613_, 13);
v_ref_632_ = l_Lean_replaceRef(v_ref_607_, v_ref_621_);
lean_inc_ref(v_inheritedTraceOptions_631_);
lean_inc(v_cancelTk_x3f_629_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc(v_maxRecDepth_620_);
lean_inc(v_currRecDepth_619_);
lean_inc_ref(v_options_618_);
lean_inc_ref(v_fileMap_617_);
lean_inc_ref(v_fileName_616_);
v___x_633_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_633_, 0, v_fileName_616_);
lean_ctor_set(v___x_633_, 1, v_fileMap_617_);
lean_ctor_set(v___x_633_, 2, v_options_618_);
lean_ctor_set(v___x_633_, 3, v_currRecDepth_619_);
lean_ctor_set(v___x_633_, 4, v_maxRecDepth_620_);
lean_ctor_set(v___x_633_, 5, v_ref_632_);
lean_ctor_set(v___x_633_, 6, v_currNamespace_622_);
lean_ctor_set(v___x_633_, 7, v_openDecls_623_);
lean_ctor_set(v___x_633_, 8, v_initHeartbeats_624_);
lean_ctor_set(v___x_633_, 9, v_maxHeartbeats_625_);
lean_ctor_set(v___x_633_, 10, v_quotContext_626_);
lean_ctor_set(v___x_633_, 11, v_currMacroScope_627_);
lean_ctor_set(v___x_633_, 12, v_cancelTk_x3f_629_);
lean_ctor_set(v___x_633_, 13, v_inheritedTraceOptions_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*14, v_diag_628_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*14 + 1, v_suppressElabErrors_630_);
v___x_634_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___x_633_, v___y_614_);
lean_dec_ref(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_635_, v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_ref_635_);
return v_res_644_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_645_; double v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_float_of_nat(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_ref_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_703_; 
v_ref_657_ = lean_ctor_get(v___y_654_, 5);
v___x_658_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_703_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_703_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_703_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v_traceState_664_; lean_object* v_env_665_; lean_object* v_nextMacroScope_666_; lean_object* v_ngen_667_; lean_object* v_auxDeclNGen_668_; lean_object* v_cache_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_702_; 
v___x_663_ = lean_st_ref_take(v___y_655_);
v_traceState_664_ = lean_ctor_get(v___x_663_, 4);
v_env_665_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_666_ = lean_ctor_get(v___x_663_, 1);
v_ngen_667_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_668_ = lean_ctor_get(v___x_663_, 3);
v_cache_669_ = lean_ctor_get(v___x_663_, 5);
v_messages_670_ = lean_ctor_get(v___x_663_, 6);
v_infoState_671_ = lean_ctor_get(v___x_663_, 7);
v_snapshotTasks_672_ = lean_ctor_get(v___x_663_, 8);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_702_ == 0)
{
v___x_674_ = v___x_663_;
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snapshotTasks_672_);
lean_inc(v_infoState_671_);
lean_inc(v_messages_670_);
lean_inc(v_cache_669_);
lean_inc(v_traceState_664_);
lean_inc(v_auxDeclNGen_668_);
lean_inc(v_ngen_667_);
lean_inc(v_nextMacroScope_666_);
lean_inc(v_env_665_);
lean_dec(v___x_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
uint64_t v_tid_676_; lean_object* v_traces_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_701_; 
v_tid_676_ = lean_ctor_get_uint64(v_traceState_664_, sizeof(void*)*1);
v_traces_677_ = lean_ctor_get(v_traceState_664_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_traceState_664_);
if (v_isSharedCheck_701_ == 0)
{
v___x_679_ = v_traceState_664_;
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_traces_677_);
lean_dec(v_traceState_664_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; double v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_683_ = 0;
v___x_684_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_685_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_685_, 0, v_cls_650_);
lean_ctor_set(v___x_685_, 1, v___x_681_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
lean_ctor_set_float(v___x_685_, sizeof(void*)*3, v___x_682_);
lean_ctor_set_float(v___x_685_, sizeof(void*)*3 + 8, v___x_682_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*3 + 16, v___x_683_);
v___x_686_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_687_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v_a_659_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_inc(v_ref_657_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_ref_657_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_PersistentArray_push___redArg(v_traces_677_, v___x_688_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_689_);
v___x_691_ = v___x_679_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_689_);
lean_ctor_set_uint64(v_reuseFailAlloc_700_, sizeof(void*)*1, v_tid_676_);
v___x_691_ = v_reuseFailAlloc_700_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 4, v___x_691_);
v___x_693_ = v___x_674_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_env_665_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_nextMacroScope_666_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_ngen_667_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_auxDeclNGen_668_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 5, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_699_, 6, v_messages_670_);
lean_ctor_set(v_reuseFailAlloc_699_, 7, v_infoState_671_);
lean_ctor_set(v_reuseFailAlloc_699_, 8, v_snapshotTasks_672_);
v___x_693_ = v_reuseFailAlloc_699_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = lean_st_ref_set(v___y_655_, v___x_693_);
v___x_695_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_695_);
v___x_697_ = v___x_661_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_704_, lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_704_, v_msg_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
if (lean_obj_tag(v_as_715_) == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_options_725_; uint8_t v_hasTrace_726_; 
v_options_725_ = lean_ctor_get(v___y_720_, 2);
v_hasTrace_726_ = lean_ctor_get_uint8(v_options_725_, sizeof(void*)*1);
if (v_hasTrace_726_ == 0)
{
lean_object* v_tail_727_; 
v_tail_727_ = lean_ctor_get(v_as_715_, 1);
lean_inc(v_tail_727_);
lean_dec_ref(v_as_715_);
v_as_715_ = v_tail_727_;
goto _start;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v_inheritedTraceOptions_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_head_729_ = lean_ctor_get(v_as_715_, 0);
lean_inc(v_head_729_);
v_tail_730_ = lean_ctor_get(v_as_715_, 1);
lean_inc(v_tail_730_);
lean_dec_ref(v_as_715_);
v_fst_731_ = lean_ctor_get(v_head_729_, 0);
lean_inc_n(v_fst_731_, 2);
v_snd_732_ = lean_ctor_get(v_head_729_, 1);
lean_inc(v_snd_732_);
lean_dec(v_head_729_);
v_inheritedTraceOptions_733_ = lean_ctor_get(v___y_720_, 13);
v___x_734_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_735_ = l_Lean_Name_append(v___x_734_, v_fst_731_);
v___x_736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_733_, v_options_725_, v___x_735_);
lean_dec(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_snd_732_);
lean_dec(v_fst_731_);
v_as_715_ = v_tail_730_;
goto _start;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_738_, 0, v_snd_732_);
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
v___x_740_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_731_, v___x_739_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_dec_ref(v___x_740_);
v_as_715_ = v_tail_730_;
goto _start;
}
else
{
lean_dec(v_tail_730_);
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_box(0);
return v___x_753_;
}
else
{
lean_object* v_key_754_; lean_object* v_value_755_; lean_object* v_tail_756_; uint8_t v___x_757_; 
v_key_754_ = lean_ctor_get(v_x_752_, 0);
v_value_755_ = lean_ctor_get(v_x_752_, 1);
v_tail_756_ = lean_ctor_get(v_x_752_, 2);
v___x_757_ = lean_name_eq(v_key_754_, v_a_751_);
if (v___x_757_ == 0)
{
v_x_752_ = v_tail_756_;
goto _start;
}
else
{
lean_object* v___x_759_; 
lean_inc(v_value_755_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v_value_755_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_760_, lean_object* v_x_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_760_, v_x_761_);
lean_dec(v_x_761_);
lean_dec(v_a_760_);
return v_res_762_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_763_; uint64_t v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1723u);
v___x_764_ = lean_uint64_of_nat(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_buckets_767_; lean_object* v___x_768_; uint64_t v___y_770_; 
v_buckets_767_ = lean_ctor_get(v_m_765_, 1);
v___x_768_ = lean_array_get_size(v_buckets_767_);
if (lean_obj_tag(v_a_766_) == 0)
{
uint64_t v___x_784_; 
v___x_784_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_770_ = v___x_784_;
goto v___jp_769_;
}
else
{
uint64_t v_hash_785_; 
v_hash_785_ = lean_ctor_get_uint64(v_a_766_, sizeof(void*)*2);
v___y_770_ = v_hash_785_;
goto v___jp_769_;
}
v___jp_769_:
{
uint64_t v___x_771_; uint64_t v___x_772_; uint64_t v_fold_773_; uint64_t v___x_774_; uint64_t v___x_775_; uint64_t v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_771_ = 32ULL;
v___x_772_ = lean_uint64_shift_right(v___y_770_, v___x_771_);
v_fold_773_ = lean_uint64_xor(v___y_770_, v___x_772_);
v___x_774_ = 16ULL;
v___x_775_ = lean_uint64_shift_right(v_fold_773_, v___x_774_);
v___x_776_ = lean_uint64_xor(v_fold_773_, v___x_775_);
v___x_777_ = lean_uint64_to_usize(v___x_776_);
v___x_778_ = lean_usize_of_nat(v___x_768_);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_sub(v___x_778_, v___x_779_);
v___x_781_ = lean_usize_land(v___x_777_, v___x_780_);
v___x_782_ = lean_array_uget_borrowed(v_buckets_767_, v___x_781_);
v___x_783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_766_, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_m_786_);
return v_res_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_789_, lean_object* v_i_790_, lean_object* v_k_791_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_array_get_size(v_keys_789_);
v___x_793_ = lean_nat_dec_lt(v_i_790_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_i_790_);
return v___x_793_;
}
else
{
lean_object* v_k_x27_794_; uint8_t v___x_795_; 
v_k_x27_794_ = lean_array_fget_borrowed(v_keys_789_, v_i_790_);
v___x_795_ = l_Lean_instBEqExtraModUse_beq(v_k_791_, v_k_x27_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_i_790_, v___x_796_);
lean_dec(v_i_790_);
v_i_790_ = v___x_797_;
goto _start;
}
else
{
lean_dec(v_i_790_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_799_, lean_object* v_i_800_, lean_object* v_k_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_799_, v_i_800_, v_k_801_);
lean_dec_ref(v_k_801_);
lean_dec_ref(v_keys_799_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; 
v___x_804_ = ((size_t)5ULL);
v___x_805_ = ((size_t)1ULL);
v___x_806_ = lean_usize_shift_left(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; 
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0);
v___x_809_ = lean_usize_sub(v___x_808_, v___x_807_);
return v___x_809_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_810_, size_t v_x_811_, lean_object* v_x_812_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v_es_813_; lean_object* v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v_j_818_; lean_object* v___x_819_; 
v_es_813_ = lean_ctor_get(v_x_810_, 0);
v___x_814_ = lean_box(2);
v___x_815_ = ((size_t)5ULL);
v___x_816_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1);
v___x_817_ = lean_usize_land(v_x_811_, v___x_816_);
v_j_818_ = lean_usize_to_nat(v___x_817_);
v___x_819_ = lean_array_get_borrowed(v___x_814_, v_es_813_, v_j_818_);
lean_dec(v_j_818_);
switch(lean_obj_tag(v___x_819_))
{
case 0:
{
lean_object* v_key_820_; uint8_t v___x_821_; 
v_key_820_ = lean_ctor_get(v___x_819_, 0);
v___x_821_ = l_Lean_instBEqExtraModUse_beq(v_x_812_, v_key_820_);
return v___x_821_;
}
case 1:
{
lean_object* v_node_822_; size_t v___x_823_; 
v_node_822_ = lean_ctor_get(v___x_819_, 0);
v___x_823_ = lean_usize_shift_right(v_x_811_, v___x_815_);
v_x_810_ = v_node_822_;
v_x_811_ = v___x_823_;
goto _start;
}
default: 
{
uint8_t v___x_825_; 
v___x_825_ = 0;
return v___x_825_;
}
}
}
else
{
lean_object* v_ks_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_ks_826_ = lean_ctor_get(v_x_810_, 0);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_826_, v___x_827_, v_x_812_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
size_t v_x_259842__boxed_832_; uint8_t v_res_833_; lean_object* v_r_834_; 
v_x_259842__boxed_832_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_res_833_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_829_, v_x_259842__boxed_832_, v_x_831_);
lean_dec_ref(v_x_831_);
lean_dec_ref(v_x_829_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint64_t v___x_837_; size_t v___x_838_; uint8_t v___x_839_; 
v___x_837_ = l_Lean_instHashableExtraModUse_hash(v_x_836_);
v___x_838_ = lean_uint64_to_usize(v___x_837_);
v___x_839_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_835_, v___x_838_, v_x_836_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_840_, v_x_841_);
lean_dec_ref(v_x_841_);
lean_dec_ref(v_x_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_847_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_848_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_855_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
lean_ctor_set(v___x_855_, 3, v___x_854_);
lean_ctor_set(v___x_855_, 4, v___x_854_);
lean_ctor_set(v___x_855_, 5, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_cls_867_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_868_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_869_ = l_Lean_Name_append(v___x_868_, v_cls_867_);
return v___x_869_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_880_, uint8_t v_isMeta_881_, lean_object* v_hint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_env_891_; uint8_t v_isExporting_892_; lean_object* v___x_893_; lean_object* v_env_894_; lean_object* v___x_895_; lean_object* v_entry_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_890_ = lean_st_ref_get(v___y_888_);
v_env_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_ref(v_env_891_);
lean_dec(v___x_890_);
v_isExporting_892_ = lean_ctor_get_uint8(v_env_891_, sizeof(void*)*8);
lean_dec_ref(v_env_891_);
v___x_893_ = lean_st_ref_get(v___y_888_);
v_env_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc_ref(v_env_894_);
lean_dec(v___x_893_);
v___x_895_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_880_);
v_entry_896_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_896_, 0, v_mod_880_);
lean_ctor_set_uint8(v_entry_896_, sizeof(void*)*1, v_isExporting_892_);
lean_ctor_set_uint8(v_entry_896_, sizeof(void*)*1 + 1, v_isMeta_881_);
v___x_897_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_898_ = lean_box(1);
v___x_899_ = lean_box(0);
v___x_942_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_895_, v___x_897_, v_env_894_, v___x_898_, v___x_899_);
v___x_943_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_942_, v_entry_896_);
lean_dec(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v_options_944_; uint8_t v_hasTrace_945_; 
v_options_944_ = lean_ctor_get(v___y_887_, 2);
v_hasTrace_945_ = lean_ctor_get_uint8(v_options_944_, sizeof(void*)*1);
if (v_hasTrace_945_ == 0)
{
lean_dec(v_hint_882_);
lean_dec(v_mod_880_);
v___y_901_ = v___y_886_;
v___y_902_ = v___y_888_;
goto v___jp_900_;
}
else
{
lean_object* v_inheritedTraceOptions_946_; lean_object* v_cls_947_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_inheritedTraceOptions_946_ = lean_ctor_get(v___y_887_, 13);
v_cls_947_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_967_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_946_, v_options_944_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v_hint_882_);
lean_dec(v_mod_880_);
v___y_901_ = v___y_886_;
v___y_902_ = v___y_888_;
goto v___jp_900_;
}
else
{
lean_object* v___x_969_; lean_object* v___y_971_; 
v___x_969_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_892_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_971_ = v___x_978_;
goto v___jp_970_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_971_ = v___x_979_;
goto v___jp_970_;
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref(v___y_971_);
v___x_972_ = l_Lean_stringToMessageData(v___y_971_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_969_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
if (v_isMeta_881_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_954_ = v___x_975_;
v___y_955_ = v___x_976_;
goto v___jp_953_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_954_ = v___x_975_;
v___y_955_ = v___x_977_;
goto v___jp_953_;
}
}
}
v___jp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___y_949_);
lean_ctor_set(v___x_951_, 1, v___y_950_);
v___x_952_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_947_, v___x_951_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_dec_ref(v___x_952_);
v___y_901_ = v___y_886_;
v___y_902_ = v___y_888_;
goto v___jp_900_;
}
else
{
lean_dec_ref(v_entry_896_);
return v___x_952_;
}
}
v___jp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
lean_inc_ref(v___y_955_);
v___x_956_ = l_Lean_stringToMessageData(v___y_955_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___y_954_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_MessageData_ofName(v_mod_880_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Lean_Name_isAnonymous(v_hint_882_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_964_ = l_Lean_MessageData_ofName(v_hint_882_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___y_949_ = v___x_961_;
v___y_950_ = v___x_965_;
goto v___jp_948_;
}
else
{
lean_object* v___x_966_; 
lean_dec(v_hint_882_);
v___x_966_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_949_ = v___x_961_;
v___y_950_ = v___x_966_;
goto v___jp_948_;
}
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec_ref(v_entry_896_);
lean_dec(v_hint_882_);
lean_dec(v_mod_880_);
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
v___jp_900_:
{
lean_object* v___x_903_; lean_object* v_toEnvExtension_904_; lean_object* v_env_905_; lean_object* v_nextMacroScope_906_; lean_object* v_ngen_907_; lean_object* v_auxDeclNGen_908_; lean_object* v_traceState_909_; lean_object* v_messages_910_; lean_object* v_infoState_911_; lean_object* v_snapshotTasks_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_940_; 
v___x_903_ = lean_st_ref_take(v___y_902_);
v_toEnvExtension_904_ = lean_ctor_get(v___x_897_, 0);
v_env_905_ = lean_ctor_get(v___x_903_, 0);
v_nextMacroScope_906_ = lean_ctor_get(v___x_903_, 1);
v_ngen_907_ = lean_ctor_get(v___x_903_, 2);
v_auxDeclNGen_908_ = lean_ctor_get(v___x_903_, 3);
v_traceState_909_ = lean_ctor_get(v___x_903_, 4);
v_messages_910_ = lean_ctor_get(v___x_903_, 6);
v_infoState_911_ = lean_ctor_get(v___x_903_, 7);
v_snapshotTasks_912_ = lean_ctor_get(v___x_903_, 8);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_903_, 5);
lean_dec(v_unused_941_);
v___x_914_ = v___x_903_;
v_isShared_915_ = v_isSharedCheck_940_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snapshotTasks_912_);
lean_inc(v_infoState_911_);
lean_inc(v_messages_910_);
lean_inc(v_traceState_909_);
lean_inc(v_auxDeclNGen_908_);
lean_inc(v_ngen_907_);
lean_inc(v_nextMacroScope_906_);
lean_inc(v_env_905_);
lean_dec(v___x_903_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_940_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_asyncMode_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v_asyncMode_916_ = lean_ctor_get(v_toEnvExtension_904_, 2);
v___x_917_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_897_, v_env_905_, v_entry_896_, v_asyncMode_916_, v___x_899_);
v___x_918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 5, v___x_918_);
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_920_ = v___x_914_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_nextMacroScope_906_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_ngen_907_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_auxDeclNGen_908_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_traceState_909_);
lean_ctor_set(v_reuseFailAlloc_939_, 5, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_939_, 6, v_messages_910_);
lean_ctor_set(v_reuseFailAlloc_939_, 7, v_infoState_911_);
lean_ctor_set(v_reuseFailAlloc_939_, 8, v_snapshotTasks_912_);
v___x_920_ = v_reuseFailAlloc_939_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_mctx_923_; lean_object* v_zetaDeltaFVarIds_924_; lean_object* v_postponed_925_; lean_object* v_diag_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
v___x_921_ = lean_st_ref_set(v___y_902_, v___x_920_);
v___x_922_ = lean_st_ref_take(v___y_901_);
v_mctx_923_ = lean_ctor_get(v___x_922_, 0);
v_zetaDeltaFVarIds_924_ = lean_ctor_get(v___x_922_, 2);
v_postponed_925_ = lean_ctor_get(v___x_922_, 3);
v_diag_926_ = lean_ctor_get(v___x_922_, 4);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_922_, 1);
lean_dec(v_unused_938_);
v___x_928_ = v___x_922_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_diag_926_);
lean_inc(v_postponed_925_);
lean_inc(v_zetaDeltaFVarIds_924_);
lean_inc(v_mctx_923_);
lean_dec(v___x_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_mctx_923_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_zetaDeltaFVarIds_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_postponed_925_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_diag_926_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_st_ref_set(v___y_901_, v___x_932_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_982_, lean_object* v_isMeta_983_, lean_object* v_hint_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v_isMeta_boxed_992_; lean_object* v_res_993_; 
v_isMeta_boxed_992_ = lean_unbox(v_isMeta_983_);
v_res_993_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_982_, v_isMeta_boxed_992_, v_hint_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_994_, lean_object* v_declName_995_, lean_object* v_as_996_, size_t v_sz_997_, size_t v_i_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_declName_995_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_b_999_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v_modules_1010_; lean_object* v___x_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v_toImport_1014_; lean_object* v_module_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1009_ = l_Lean_Environment_header(v___x_994_);
v_modules_1010_ = lean_ctor_get(v___x_1009_, 3);
lean_inc_ref(v_modules_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1012_ = lean_array_uget_borrowed(v_as_996_, v_i_998_);
v___x_1013_ = lean_array_get(v___x_1011_, v_modules_1010_, v_a_1012_);
lean_dec_ref(v_modules_1010_);
v_toImport_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_toImport_1014_);
lean_dec(v___x_1013_);
v_module_1015_ = lean_ctor_get(v_toImport_1014_, 0);
lean_inc(v_module_1015_);
lean_dec_ref(v_toImport_1014_);
v___x_1016_ = 0;
lean_inc(v_declName_995_);
v___x_1017_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1015_, v___x_1016_, v_declName_995_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; 
lean_dec_ref(v___x_1017_);
v___x_1018_ = lean_box(0);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_add(v_i_998_, v___x_1019_);
v_i_998_ = v___x_1020_;
v_b_999_ = v___x_1018_;
goto _start;
}
else
{
lean_dec(v_declName_995_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1022_, lean_object* v_declName_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1022_, v_declName_1023_, v_as_1024_, v_sz_boxed_1035_, v_i_boxed_1036_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_as_1024_);
lean_dec_ref(v___x_1022_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1041_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1042_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1045_, uint8_t v_isMeta_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v_env_1058_; lean_object* v___y_1060_; lean_object* v___x_1073_; 
v___x_1054_ = lean_st_ref_get(v___y_1052_);
v_env_1058_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_ref(v_env_1058_);
lean_dec(v___x_1054_);
v___x_1073_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1058_, v_declName_1045_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_dec_ref(v_env_1058_);
lean_dec(v_declName_1045_);
goto v___jp_1055_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v_modules_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_val_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_val_1074_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = l_Lean_Environment_header(v_env_1058_);
v_modules_1076_ = lean_ctor_get(v___x_1075_, 3);
lean_inc_ref(v_modules_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = lean_array_get_size(v_modules_1076_);
v___x_1078_ = lean_nat_dec_lt(v_val_1074_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v_modules_1076_);
lean_dec(v_val_1074_);
lean_dec_ref(v_env_1058_);
lean_dec(v_declName_1045_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1079_; lean_object* v_env_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___y_1084_; 
v___x_1079_ = lean_st_ref_get(v___y_1052_);
v_env_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_env_1080_);
lean_dec(v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1082_ = lean_array_fget(v_modules_1076_, v_val_1074_);
lean_dec(v_val_1074_);
lean_dec_ref(v_modules_1076_);
if (v_isMeta_1046_ == 0)
{
lean_dec_ref(v_env_1080_);
v___y_1084_ = v_isMeta_1046_;
goto v___jp_1083_;
}
else
{
uint8_t v___x_1095_; 
lean_inc(v_declName_1045_);
v___x_1095_ = l_Lean_isMarkedMeta(v_env_1080_, v_declName_1045_);
if (v___x_1095_ == 0)
{
v___y_1084_ = v_isMeta_1046_;
goto v___jp_1083_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = 0;
v___y_1084_ = v___x_1096_;
goto v___jp_1083_;
}
}
v___jp_1083_:
{
lean_object* v_toImport_1085_; lean_object* v_module_1086_; lean_object* v___x_1087_; 
v_toImport_1085_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_toImport_1085_);
lean_dec(v___x_1082_);
v_module_1086_ = lean_ctor_get(v_toImport_1085_, 0);
lean_inc(v_module_1086_);
lean_dec_ref(v_toImport_1085_);
lean_inc(v_declName_1045_);
v___x_1087_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1086_, v___y_1084_, v_declName_1045_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v___x_1087_);
v___x_1088_ = l_Lean_indirectModUseExt;
v___x_1089_ = lean_box(1);
v___x_1090_ = lean_box(0);
lean_inc_ref(v_env_1058_);
v___x_1091_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1081_, v___x_1088_, v_env_1058_, v___x_1089_, v___x_1090_);
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1091_, v_declName_1045_);
lean_dec(v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1060_ = v___x_1093_;
goto v___jp_1059_;
}
else
{
lean_object* v_val_1094_; 
v_val_1094_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1094_);
lean_dec_ref(v___x_1092_);
v___y_1060_ = v_val_1094_;
goto v___jp_1059_;
}
}
else
{
lean_dec_ref(v_env_1058_);
lean_dec(v_declName_1045_);
return v___x_1087_;
}
}
}
}
v___jp_1055_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
v___jp_1059_:
{
lean_object* v___x_1061_; size_t v_sz_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_box(0);
v_sz_1062_ = lean_array_size(v___y_1060_);
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1058_, v_declName_1045_, v___y_1060_, v_sz_1062_, v___x_1063_, v___x_1061_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_env_1058_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1064_, 0);
lean_dec(v_unused_1072_);
v___x_1066_ = v___x_1064_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v___x_1064_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1061_);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1061_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1097_, lean_object* v_isMeta_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_isMeta_boxed_1106_; lean_object* v_res_1107_; 
v_isMeta_boxed_1106_ = lean_unbox(v_isMeta_1098_);
v_res_1107_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1097_, v_isMeta_boxed_1106_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
if (lean_obj_tag(v_as_x27_1108_) == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_b_1109_);
return v___x_1117_;
}
else
{
lean_object* v_head_1118_; lean_object* v_tail_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v_head_1118_ = lean_ctor_get(v_as_x27_1108_, 0);
lean_inc(v_head_1118_);
v_tail_1119_ = lean_ctor_get(v_as_x27_1108_, 1);
lean_inc(v_tail_1119_);
lean_dec_ref(v_as_x27_1108_);
v___x_1120_ = 1;
v___x_1121_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1118_, v___x_1120_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v___x_1121_);
v___x_1122_ = lean_box(0);
v_as_x27_1108_ = v_tail_1119_;
v_b_1109_ = v___x_1122_;
goto _start;
}
else
{
lean_dec(v_tail_1119_);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1124_, v_b_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1134_, lean_object* v_currNamespace_1135_, lean_object* v_openDecls_1136_, lean_object* v_n_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l_Lean_ResolveName_resolveNamespace(v_env_1134_, v_currNamespace_1135_, v_openDecls_1136_, v_n_1137_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___y_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1142_, lean_object* v_currNamespace_1143_, lean_object* v_openDecls_1144_, lean_object* v_n_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1142_, v_currNamespace_1143_, v_openDecls_1144_, v_n_1145_, v___y_1146_, v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_currNamespace_1149_);
lean_ctor_set(v___x_1152_, 1, v___y_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1153_, v___y_1154_, v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1157_, lean_object* v_options_1158_, lean_object* v_currNamespace_1159_, lean_object* v_openDecls_1160_, lean_object* v_n_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = l_Lean_ResolveName_resolveGlobalName(v_env_1157_, v_options_1158_, v_currNamespace_1159_, v_openDecls_1160_, v_n_1161_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1166_, lean_object* v_options_1167_, lean_object* v_currNamespace_1168_, lean_object* v_openDecls_1169_, lean_object* v_n_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1166_, v_options_1167_, v_currNamespace_1168_, v_openDecls_1169_, v_n_1170_, v___y_1171_, v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_options_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_env_1184_; lean_object* v_options_1185_; lean_object* v_currRecDepth_1186_; lean_object* v_maxRecDepth_1187_; lean_object* v_ref_1188_; lean_object* v_currNamespace_1189_; lean_object* v_openDecls_1190_; lean_object* v_quotContext_1191_; lean_object* v_currMacroScope_1192_; lean_object* v___x_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v_methods_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1183_ = lean_st_ref_get(v___y_1181_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref_n(v_env_1184_, 4);
lean_dec(v___x_1183_);
v_options_1185_ = lean_ctor_get(v___y_1180_, 2);
v_currRecDepth_1186_ = lean_ctor_get(v___y_1180_, 3);
v_maxRecDepth_1187_ = lean_ctor_get(v___y_1180_, 4);
v_ref_1188_ = lean_ctor_get(v___y_1180_, 5);
v_currNamespace_1189_ = lean_ctor_get(v___y_1180_, 6);
v_openDecls_1190_ = lean_ctor_get(v___y_1180_, 7);
v_quotContext_1191_ = lean_ctor_get(v___y_1180_, 10);
v_currMacroScope_1192_ = lean_ctor_get(v___y_1180_, 11);
v___x_1193_ = lean_st_ref_get(v___y_1181_);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1193_, 1);
lean_inc(v_nextMacroScope_1194_);
lean_dec(v___x_1193_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1195_, 0, v_env_1184_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1196_, 0, v_env_1184_);
lean_inc_n(v_openDecls_1190_, 2);
lean_inc_n(v_currNamespace_1189_, 3);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1197_, 0, v_env_1184_);
lean_closure_set(v___f_1197_, 1, v_currNamespace_1189_);
lean_closure_set(v___f_1197_, 2, v_openDecls_1190_);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1198_, 0, v_currNamespace_1189_);
lean_inc_ref(v_options_1185_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1199_, 0, v_env_1184_);
lean_closure_set(v___f_1199_, 1, v_options_1185_);
lean_closure_set(v___f_1199_, 2, v_currNamespace_1189_);
lean_closure_set(v___f_1199_, 3, v_openDecls_1190_);
v_methods_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1200_, 0, v___f_1195_);
lean_ctor_set(v_methods_1200_, 1, v___f_1198_);
lean_ctor_set(v_methods_1200_, 2, v___f_1196_);
lean_ctor_set(v_methods_1200_, 3, v___f_1197_);
lean_ctor_set(v_methods_1200_, 4, v___f_1199_);
lean_inc(v_ref_1188_);
lean_inc(v_maxRecDepth_1187_);
lean_inc(v_currRecDepth_1186_);
lean_inc(v_currMacroScope_1192_);
lean_inc(v_quotContext_1191_);
v___x_1201_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1201_, 0, v_methods_1200_);
lean_ctor_set(v___x_1201_, 1, v_quotContext_1191_);
lean_ctor_set(v___x_1201_, 2, v_currMacroScope_1192_);
lean_ctor_set(v___x_1201_, 3, v_currRecDepth_1186_);
lean_ctor_set(v___x_1201_, 4, v_maxRecDepth_1187_);
lean_ctor_set(v___x_1201_, 5, v_ref_1188_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1203_, 0, v_nextMacroScope_1194_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
v___x_1204_ = lean_apply_2(v_x_1175_, v___x_1201_, v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v_a_1206_; lean_object* v_macroScope_1207_; lean_object* v_traceMsgs_1208_; lean_object* v_expandedMacroDecls_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 1);
lean_inc(v_a_1205_);
v_a_1206_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1204_);
v_macroScope_1207_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_macroScope_1207_);
v_traceMsgs_1208_ = lean_ctor_get(v_a_1205_, 1);
lean_inc(v_traceMsgs_1208_);
v_expandedMacroDecls_1209_ = lean_ctor_get(v_a_1205_, 2);
lean_inc(v_expandedMacroDecls_1209_);
lean_dec(v_a_1205_);
v___x_1210_ = lean_box(0);
v___x_1211_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1209_, v___x_1210_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v_env_1213_; lean_object* v_ngen_1214_; lean_object* v_auxDeclNGen_1215_; lean_object* v_traceState_1216_; lean_object* v_cache_1217_; lean_object* v_messages_1218_; lean_object* v_infoState_1219_; lean_object* v_snapshotTasks_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v___x_1211_);
v___x_1212_ = lean_st_ref_take(v___y_1181_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
v_ngen_1214_ = lean_ctor_get(v___x_1212_, 2);
v_auxDeclNGen_1215_ = lean_ctor_get(v___x_1212_, 3);
v_traceState_1216_ = lean_ctor_get(v___x_1212_, 4);
v_cache_1217_ = lean_ctor_get(v___x_1212_, 5);
v_messages_1218_ = lean_ctor_get(v___x_1212_, 6);
v_infoState_1219_ = lean_ctor_get(v___x_1212_, 7);
v_snapshotTasks_1220_ = lean_ctor_get(v___x_1212_, 8);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1212_, 1);
lean_dec(v_unused_1247_);
v___x_1222_ = v___x_1212_;
v_isShared_1223_ = v_isSharedCheck_1246_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_snapshotTasks_1220_);
lean_inc(v_infoState_1219_);
lean_inc(v_messages_1218_);
lean_inc(v_cache_1217_);
lean_inc(v_traceState_1216_);
lean_inc(v_auxDeclNGen_1215_);
lean_inc(v_ngen_1214_);
lean_inc(v_env_1213_);
lean_dec(v___x_1212_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1246_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_macroScope_1207_);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_env_1213_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_macroScope_1207_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_ngen_1214_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_auxDeclNGen_1215_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_traceState_1216_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v_cache_1217_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_messages_1218_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_infoState_1219_);
lean_ctor_set(v_reuseFailAlloc_1245_, 8, v_snapshotTasks_1220_);
v___x_1225_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_st_ref_set(v___y_1181_, v___x_1225_);
v___x_1227_ = l_List_reverse___redArg(v_traceMsgs_1208_);
v___x_1228_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1227_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_a_1206_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1206_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_a_1206_);
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_traceMsgs_1208_);
lean_dec(v_macroScope_1207_);
lean_dec(v_a_1206_);
v_a_1248_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1211_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1211_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; 
v_a_1256_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1204_);
if (lean_obj_tag(v_a_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v_a_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_a_1257_ = lean_ctor_get(v_a_1256_, 0);
lean_inc(v_a_1257_);
v_a_1258_ = lean_ctor_get(v_a_1256_, 1);
lean_inc_ref(v_a_1258_);
lean_dec_ref(v_a_1256_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1260_ = lean_string_dec_eq(v_a_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_a_1258_);
v___x_1262_ = l_Lean_MessageData_ofFormat(v___x_1261_);
v___x_1263_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1257_, v___x_1262_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v_a_1257_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; 
lean_dec_ref(v_a_1258_);
v___x_1264_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1257_);
return v___x_1264_;
}
}
else
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_bs_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1279_, v_sz_1278_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_bs_1280_);
return v___x_1282_;
}
else
{
lean_object* v_v_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_v_1283_ = lean_array_uget(v_bs_1280_, v_i_1279_);
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1283_);
v___x_1285_ = l_Lean_Syntax_isOfKind(v_v_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v_v_1283_);
lean_dec_ref(v_bs_1280_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = l_Lean_Syntax_getArg(v_v_1283_, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_isOfKind(v___x_1288_, v___x_1284_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_v_1283_);
lean_dec_ref(v_bs_1280_);
v___x_1290_ = lean_box(0);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v_bs_x27_1292_; lean_object* v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1291_ = lean_unsigned_to_nat(3u);
v_bs_x27_1292_ = lean_array_uset(v_bs_1280_, v_i_1279_, v___x_1287_);
v___x_1293_ = l_Lean_Syntax_getArg(v_v_1283_, v___x_1291_);
lean_dec(v_v_1283_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1279_, v___x_1294_);
v___x_1296_ = lean_array_uset(v_bs_x27_1292_, v_i_1279_, v___x_1293_);
v_i_1279_ = v___x_1295_;
v_bs_1280_ = v___x_1296_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_bs_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1301_, v_i_boxed_1302_, v_bs_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_bs_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_bs_1318_);
return v___x_1320_;
}
else
{
lean_object* v_v_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_v_1321_ = lean_array_uget(v_bs_1318_, v_i_1317_);
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1321_);
v___x_1323_ = l_Lean_Syntax_isOfKind(v_v_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_v_1321_);
lean_dec_ref(v_bs_1318_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = l_Lean_Syntax_getArg(v_v_1321_, v___x_1325_);
v___x_1327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1328_ = l_Lean_Syntax_isOfKind(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v_v_1321_);
lean_dec_ref(v_bs_1318_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_bs_x27_1332_; lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_unsigned_to_nat(0u);
v_bs_x27_1332_ = lean_array_uset(v_bs_1318_, v_i_1317_, v___x_1331_);
v___x_1333_ = l_Lean_Syntax_getArg(v_v_1321_, v___x_1330_);
lean_dec(v_v_1321_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1317_, v___x_1334_);
v___x_1336_ = lean_array_uset(v_bs_x27_1332_, v_i_1317_, v___x_1333_);
v_i_1317_ = v___x_1335_;
v_bs_1318_ = v___x_1336_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1338_, lean_object* v_i_1339_, lean_object* v_bs_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1338_);
lean_dec(v_sz_1338_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1341_, v_i_boxed_1342_, v_bs_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1350_, size_t v_i_1351_, lean_object* v_bs_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_usize_dec_lt(v_i_1351_, v_sz_1350_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_bs_1352_);
return v___x_1354_;
}
else
{
lean_object* v_v_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_v_1355_ = lean_array_uget(v_bs_1352_, v_i_1351_);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1355_);
v___x_1357_ = l_Lean_Syntax_isOfKind(v_v_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v_v_1355_);
lean_dec_ref(v_bs_1352_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v_bs_x27_1360_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v_bs_x27_1360_ = lean_array_uset(v_bs_1352_, v_i_1351_, v___x_1359_);
v___x_1367_ = l_Lean_Syntax_getArg(v_v_1355_, v___x_1359_);
lean_dec(v_v_1355_);
v___x_1368_ = l_Lean_Syntax_isNone(v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(2u);
v___x_1370_ = l_Lean_Syntax_matchesNull(v___x_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v_bs_x27_1360_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
goto v___jp_1361_;
}
}
else
{
lean_dec(v___x_1367_);
goto v___jp_1361_;
}
v___jp_1361_:
{
lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1351_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1360_, v_i_1351_, v___x_1362_);
v_i_1351_ = v___x_1364_;
v_bs_1352_ = v___x_1365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1372_, lean_object* v_i_1373_, lean_object* v_bs_1374_){
_start:
{
size_t v_sz_boxed_1375_; size_t v_i_boxed_1376_; lean_object* v_res_1377_; 
v_sz_boxed_1375_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1376_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1375_, v_i_boxed_1376_, v_bs_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1378_, size_t v_i_1379_, lean_object* v_bs_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_usize_dec_lt(v_i_1379_, v_sz_1378_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_bs_1380_);
return v___x_1382_;
}
else
{
lean_object* v_v_1383_; lean_object* v___x_1384_; lean_object* v_bs_x27_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v_v_1383_ = lean_array_uget(v_bs_1380_, v_i_1379_);
v___x_1384_ = lean_unsigned_to_nat(0u);
v_bs_x27_1385_ = lean_array_uset(v_bs_1380_, v_i_1379_, v___x_1384_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1379_, v___x_1386_);
v___x_1388_ = lean_array_uset(v_bs_x27_1385_, v_i_1379_, v_v_1383_);
v_i_1379_ = v___x_1387_;
v_bs_1380_ = v___x_1388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_bs_1392_){
_start:
{
size_t v_sz_boxed_1393_; size_t v_i_boxed_1394_; lean_object* v_res_1395_; 
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1393_, v_i_boxed_1394_, v_bs_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1397_, v___y_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1401_, v_x_1402_, v___y_1403_, v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v_x_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1409_, lean_object* v_as_x27_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
if (lean_obj_tag(v_as_x27_1410_) == 0)
{
lean_object* v___x_1419_; 
lean_dec(v_stx_1409_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_b_1411_);
return v___x_1419_;
}
else
{
lean_object* v_head_1420_; lean_object* v_tail_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v_b_1411_);
v_head_1420_ = lean_ctor_get(v_as_x27_1410_, 0);
v_tail_1421_ = lean_ctor_get(v_as_x27_1410_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_as_x27_1410_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1423_ = v_as_x27_1410_;
v_isShared_1424_ = v_isSharedCheck_1463_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_tail_1421_);
lean_inc(v_head_1420_);
lean_dec(v_as_x27_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1463_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_value_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_value_1425_ = lean_ctor_get(v_head_1420_, 1);
lean_inc(v_value_1425_);
lean_dec(v_head_1420_);
v___x_1426_ = lean_box(0);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v_stx_1409_);
v___x_1427_ = lean_apply_8(v_value_1425_, v_stx_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, lean_box(0));
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1428_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 0);
lean_ctor_set(v___x_1423_, 1, v___x_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1432_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1426_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1462_; 
lean_del_object(v___x_1423_);
v_a_1440_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1442_ = v___x_1427_;
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1427_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___y_1447_; uint8_t v___x_1460_; 
v___x_1444_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1445_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1460_ = l_Lean_Exception_isInterrupt(v_a_1440_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
lean_inc(v_a_1440_);
v___x_1461_ = l_Lean_Exception_isRuntime(v_a_1440_);
v___y_1447_ = v___x_1461_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___x_1460_;
goto v___jp_1446_;
}
v___jp_1446_:
{
if (v___y_1447_ == 0)
{
if (lean_obj_tag(v_a_1440_) == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
if (v_isShared_1443_ == 0)
{
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1440_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v_id_1451_; uint8_t v___x_1452_; 
v_id_1451_ = lean_ctor_get(v_a_1440_, 0);
v___x_1452_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1445_, v_id_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
if (v_isShared_1443_ == 0)
{
v___x_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1440_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
else
{
lean_dec_ref(v_a_1440_);
lean_del_object(v___x_1442_);
v_as_x27_1410_ = v_tail_1421_;
v_b_1411_ = v___x_1444_;
goto _start;
}
}
}
else
{
lean_object* v___x_1458_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
if (v_isShared_1443_ == 0)
{
v___x_1458_ = v___x_1442_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1440_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1464_, lean_object* v_as_x27_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1464_, v_as_x27_1465_, v_b_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1477_, lean_object* v_rhs_x3f_1478_, lean_object* v_otherwise_x3f_1479_, lean_object* v_body_x3f_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v___y_1489_; uint8_t v___y_1490_; uint8_t v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v_body_1499_; lean_object* v___y_1519_; lean_object* v_otherwise_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v_rhs_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; 
if (lean_obj_tag(v_rhs_x3f_1478_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v_rhs_1532_ = v___x_1543_;
v___y_1533_ = v_a_1481_;
v___y_1534_ = v_a_1482_;
v___y_1535_ = v_a_1483_;
v___y_1536_ = v_a_1484_;
v___y_1537_ = v_a_1485_;
v___y_1538_ = v_a_1486_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1544_; lean_object* v___x_1545_; 
v_val_1544_ = lean_ctor_get(v_rhs_x3f_1478_, 0);
lean_inc(v_val_1544_);
lean_dec_ref(v_rhs_x3f_1478_);
v___x_1545_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1544_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v_rhs_1532_ = v_a_1546_;
v___y_1533_ = v_a_1481_;
v___y_1534_ = v_a_1482_;
v___y_1535_ = v_a_1483_;
v___y_1536_ = v_a_1484_;
v___y_1537_ = v_a_1485_;
v___y_1538_ = v_a_1486_;
goto v___jp_1531_;
}
else
{
lean_dec(v_body_x3f_1480_);
lean_dec(v_otherwise_x3f_1479_);
lean_dec_ref(v_reassigned_1477_);
return v___x_1545_;
}
}
v___jp_1488_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1494_, 0, v___y_1492_);
lean_ctor_set(v___x_1494_, 1, v___y_1493_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2, v___y_1489_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2 + 1, v___y_1491_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2 + 2, v___y_1490_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
v___jp_1496_:
{
lean_object* v___x_1500_; lean_object* v_info_1501_; uint8_t v_breaks_1502_; uint8_t v_continues_1503_; uint8_t v_returnsEarly_1504_; lean_object* v_numRegularExits_1505_; lean_object* v_reassigns_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1500_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1499_, v___y_1497_);
v_info_1501_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1498_, v___x_1500_);
v_breaks_1502_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2);
v_continues_1503_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2 + 1);
v_returnsEarly_1504_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2 + 2);
v_numRegularExits_1505_ = lean_ctor_get(v_info_1501_, 0);
lean_inc(v_numRegularExits_1505_);
v_reassigns_1506_ = lean_ctor_get(v_info_1501_, 1);
lean_inc(v_reassigns_1506_);
lean_dec_ref(v_info_1501_);
v_sz_1507_ = lean_array_size(v_reassigned_1477_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1507_, v___x_1508_, v_reassigned_1477_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_array_get_size(v___x_1509_);
v___x_1512_ = lean_nat_dec_lt(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_breaks_1502_;
v___y_1490_ = v_returnsEarly_1504_;
v___y_1491_ = v_continues_1503_;
v___y_1492_ = v_numRegularExits_1505_;
v___y_1493_ = v_reassigns_1506_;
goto v___jp_1488_;
}
else
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_le(v___x_1511_, v___x_1511_);
if (v___x_1513_ == 0)
{
if (v___x_1512_ == 0)
{
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_breaks_1502_;
v___y_1490_ = v_returnsEarly_1504_;
v___y_1491_ = v_continues_1503_;
v___y_1492_ = v_numRegularExits_1505_;
v___y_1493_ = v_reassigns_1506_;
goto v___jp_1488_;
}
else
{
size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_usize_of_nat(v___x_1511_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1509_, v___x_1508_, v___x_1514_, v_reassigns_1506_);
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_breaks_1502_;
v___y_1490_ = v_returnsEarly_1504_;
v___y_1491_ = v_continues_1503_;
v___y_1492_ = v_numRegularExits_1505_;
v___y_1493_ = v___x_1515_;
goto v___jp_1488_;
}
}
else
{
size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_usize_of_nat(v___x_1511_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1509_, v___x_1508_, v___x_1516_, v_reassigns_1506_);
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_breaks_1502_;
v___y_1490_ = v_returnsEarly_1504_;
v___y_1491_ = v_continues_1503_;
v___y_1492_ = v_numRegularExits_1505_;
v___y_1493_ = v___x_1517_;
goto v___jp_1488_;
}
}
}
v___jp_1518_:
{
if (lean_obj_tag(v_body_x3f_1480_) == 0)
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___y_1497_ = v_otherwise_1520_;
v___y_1498_ = v___y_1519_;
v_body_1499_ = v___x_1527_;
goto v___jp_1496_;
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1529_; 
v_val_1528_ = lean_ctor_get(v_body_x3f_1480_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v_body_x3f_1480_);
v___x_1529_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1528_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___y_1497_ = v_otherwise_1520_;
v___y_1498_ = v___y_1519_;
v_body_1499_ = v_a_1530_;
goto v___jp_1496_;
}
else
{
lean_dec_ref(v_otherwise_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_reassigned_1477_);
return v___x_1529_;
}
}
}
v___jp_1531_:
{
if (lean_obj_tag(v_otherwise_x3f_1479_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___y_1519_ = v_rhs_1532_;
v_otherwise_1520_ = v___x_1539_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1534_;
v___y_1523_ = v___y_1535_;
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1538_;
goto v___jp_1518_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; 
v_val_1540_ = lean_ctor_get(v_otherwise_x3f_1479_, 0);
lean_inc(v_val_1540_);
lean_dec_ref(v_otherwise_x3f_1479_);
v___x_1541_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1540_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___y_1519_ = v_rhs_1532_;
v_otherwise_1520_ = v_a_1542_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1534_;
v___y_1523_ = v___y_1535_;
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1538_;
goto v___jp_1518_;
}
else
{
lean_dec_ref(v_rhs_1532_);
lean_dec(v_body_x3f_1480_);
lean_dec_ref(v_reassigned_1477_);
return v___x_1541_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1643_, lean_object* v_decl_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v_reassigns_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1644_);
v___x_1681_ = l_Lean_Syntax_isOfKind(v_decl_1644_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1644_);
v___x_1683_ = l_Lean_Syntax_isOfKind(v_decl_1644_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1684_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1685_ = lean_box(0);
v___x_1686_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1685_, v___x_1683_);
v___x_1687_ = l_Std_Format_defWidth;
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = l_Std_Format_pretty(v___x_1686_, v___x_1687_, v___x_1688_, v___x_1688_);
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1684_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1691_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v_pattern_1694_; lean_object* v___y_1696_; lean_object* v_otherwise_x3f_1697_; lean_object* v_body_x3f_x3f_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v_body_x3f_x3f_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___x_1728_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v_pattern_1694_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1693_);
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1767_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1728_);
v___x_1768_ = l_Lean_Syntax_isNone(v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
lean_inc(v___x_1767_);
v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1728_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v___x_1767_);
lean_dec(v_pattern_1694_);
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1771_ = lean_box(0);
v___x_1772_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1771_, v___x_1769_);
v___x_1773_ = l_Std_Format_defWidth;
v___x_1774_ = l_Std_Format_pretty(v___x_1772_, v___x_1773_, v___x_1693_, v___x_1693_);
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1770_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1776_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1778_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1693_);
lean_dec(v___x_1767_);
v___x_1779_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1780_ = l_Lean_Syntax_isOfKind(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v_pattern_1694_);
v___x_1781_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1782_ = lean_box(0);
v___x_1783_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1782_, v___x_1780_);
v___x_1784_ = l_Std_Format_defWidth;
v___x_1785_ = l_Std_Format_pretty(v___x_1783_, v___x_1784_, v___x_1693_, v___x_1693_);
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1781_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1787_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1788_;
}
else
{
v___y_1730_ = v_a_1645_;
v___y_1731_ = v_a_1646_;
v___y_1732_ = v_a_1647_;
v___y_1733_ = v_a_1648_;
v___y_1734_ = v_a_1649_;
v___y_1735_ = v_a_1650_;
goto v___jp_1729_;
}
}
}
else
{
lean_dec(v___x_1767_);
v___y_1730_ = v_a_1645_;
v___y_1731_ = v_a_1646_;
v___y_1732_ = v_a_1647_;
v___y_1733_ = v_a_1648_;
v___y_1734_ = v_a_1649_;
v___y_1735_ = v_a_1650_;
goto v___jp_1729_;
}
v___jp_1695_:
{
if (v_reassignment_1643_ == 0)
{
lean_object* v___x_1705_; 
lean_dec(v_pattern_1694_);
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1665_ = v_body_x3f_x3f_1698_;
v___y_1666_ = v_otherwise_x3f_1697_;
v___y_1667_ = v___y_1696_;
v_reassigns_1668_ = v___x_1705_;
v___y_1669_ = v___y_1699_;
v___y_1670_ = v___y_1700_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___y_1703_;
v___y_1674_ = v___y_1704_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1694_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
v___y_1665_ = v_body_x3f_x3f_1698_;
v___y_1666_ = v_otherwise_x3f_1697_;
v___y_1667_ = v___y_1696_;
v_reassigns_1668_ = v_a_1707_;
v___y_1669_ = v___y_1699_;
v___y_1670_ = v___y_1700_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___y_1703_;
v___y_1674_ = v___y_1704_;
goto v___jp_1664_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_body_x3f_x3f_1698_);
lean_dec(v_otherwise_x3f_1697_);
lean_dec(v___y_1696_);
v_a_1708_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1706_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
v___jp_1716_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1717_);
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_body_x3f_x3f_1719_);
v___y_1696_ = v___y_1718_;
v_otherwise_x3f_1697_ = v___x_1726_;
v_body_x3f_x3f_1698_ = v___x_1727_;
v___y_1699_ = v___y_1720_;
v___y_1700_ = v___y_1721_;
v___y_1701_ = v___y_1722_;
v___y_1702_ = v___y_1723_;
v___y_1703_ = v___y_1724_;
v___y_1704_ = v___y_1725_;
goto v___jp_1695_;
}
v___jp_1729_:
{
lean_object* v___x_1736_; lean_object* v_rhs_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1736_ = lean_unsigned_to_nat(3u);
v_rhs_1737_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1736_);
v___x_1738_ = lean_unsigned_to_nat(4u);
v___x_1739_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1738_);
v___x_1740_ = l_Lean_Syntax_isNone(v___x_1739_);
if (v___x_1740_ == 0)
{
uint8_t v___x_1741_; 
lean_inc(v___x_1739_);
v___x_1741_ = l_Lean_Syntax_matchesNull(v___x_1739_, v___x_1736_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1739_);
lean_dec(v_rhs_1737_);
lean_dec(v_pattern_1694_);
v___x_1742_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1743_ = lean_box(0);
v___x_1744_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1743_, v___x_1741_);
v___x_1745_ = l_Std_Format_defWidth;
v___x_1746_ = l_Std_Format_pretty(v___x_1744_, v___x_1745_, v___x_1693_, v___x_1693_);
v___x_1747_ = l_Lean_stringToMessageData(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1742_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1748_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; lean_object* v_otherwise_x3f_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1750_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1751_ = l_Lean_Syntax_getArg(v___x_1739_, v___x_1728_);
v___x_1752_ = l_Lean_Syntax_getArg(v___x_1739_, v___x_1750_);
lean_dec(v___x_1739_);
v___x_1753_ = l_Lean_Syntax_isNone(v___x_1752_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; 
lean_inc(v___x_1752_);
v___x_1754_ = l_Lean_Syntax_matchesNull(v___x_1752_, v___x_1728_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v___x_1752_);
lean_dec(v_otherwise_x3f_1751_);
lean_dec(v_rhs_1737_);
lean_dec(v_pattern_1694_);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1756_ = lean_box(0);
v___x_1757_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1756_, v___x_1754_);
v___x_1758_ = l_Std_Format_defWidth;
v___x_1759_ = l_Std_Format_pretty(v___x_1757_, v___x_1758_, v___x_1693_, v___x_1693_);
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1755_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1761_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1762_;
}
else
{
lean_object* v_body_x3f_x3f_1763_; lean_object* v___x_1764_; 
lean_dec(v_decl_1644_);
v_body_x3f_x3f_1763_ = l_Lean_Syntax_getArg(v___x_1752_, v___x_1693_);
lean_dec(v___x_1752_);
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_body_x3f_x3f_1763_);
v___y_1717_ = v_otherwise_x3f_1751_;
v___y_1718_ = v_rhs_1737_;
v_body_x3f_x3f_1719_ = v___x_1764_;
v___y_1720_ = v___y_1730_;
v___y_1721_ = v___y_1731_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___y_1734_;
v___y_1725_ = v___y_1735_;
goto v___jp_1716_;
}
}
else
{
lean_object* v___x_1765_; 
lean_dec(v___x_1752_);
lean_dec(v_decl_1644_);
v___x_1765_ = lean_box(0);
v___y_1717_ = v_otherwise_x3f_1751_;
v___y_1718_ = v_rhs_1737_;
v_body_x3f_x3f_1719_ = v___x_1765_;
v___y_1720_ = v___y_1730_;
v___y_1721_ = v___y_1731_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___y_1734_;
v___y_1725_ = v___y_1735_;
goto v___jp_1716_;
}
}
}
else
{
lean_object* v___x_1766_; 
lean_dec(v___x_1739_);
lean_dec(v_decl_1644_);
v___x_1766_ = lean_box(0);
v___y_1696_ = v_rhs_1737_;
v_otherwise_x3f_1697_ = v___x_1766_;
v_body_x3f_x3f_1698_ = v___x_1766_;
v___y_1699_ = v___y_1730_;
v___y_1700_ = v___y_1731_;
v___y_1701_ = v___y_1732_;
v___y_1702_ = v___y_1733_;
v___y_1703_ = v___y_1734_;
v___y_1704_ = v___y_1735_;
goto v___jp_1695_;
}
}
}
}
else
{
lean_object* v___x_1789_; lean_object* v_x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1789_ = lean_unsigned_to_nat(0u);
v_x_1790_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1789_);
v___x_1804_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1790_);
v___x_1805_ = l_Lean_Syntax_isOfKind(v_x_1790_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v_x_1790_);
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1807_ = lean_box(0);
v___x_1808_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1807_, v___x_1805_);
v___x_1809_ = l_Std_Format_defWidth;
v___x_1810_ = l_Std_Format_pretty(v___x_1808_, v___x_1809_, v___x_1789_, v___x_1789_);
v___x_1811_ = l_Lean_stringToMessageData(v___x_1810_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1806_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1812_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1814_);
v___x_1816_ = l_Lean_Syntax_isNone(v___x_1815_);
if (v___x_1816_ == 0)
{
uint8_t v___x_1817_; 
lean_inc(v___x_1815_);
v___x_1817_ = l_Lean_Syntax_matchesNull(v___x_1815_, v___x_1814_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1815_);
lean_dec(v_x_1790_);
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1819_ = lean_box(0);
v___x_1820_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1819_, v___x_1817_);
v___x_1821_ = l_Std_Format_defWidth;
v___x_1822_ = l_Std_Format_pretty(v___x_1820_, v___x_1821_, v___x_1789_, v___x_1789_);
v___x_1823_ = l_Lean_stringToMessageData(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1818_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1824_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1815_, v___x_1789_);
lean_dec(v___x_1815_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1828_ = l_Lean_Syntax_isOfKind(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v_x_1790_);
v___x_1829_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Lean_Syntax_formatStx(v_decl_1644_, v___x_1830_, v___x_1828_);
v___x_1832_ = l_Std_Format_defWidth;
v___x_1833_ = l_Std_Format_pretty(v___x_1831_, v___x_1832_, v___x_1789_, v___x_1789_);
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1829_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1835_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1836_;
}
else
{
v___y_1792_ = v_a_1645_;
v___y_1793_ = v_a_1646_;
v___y_1794_ = v_a_1647_;
v___y_1795_ = v_a_1648_;
v___y_1796_ = v_a_1649_;
v___y_1797_ = v_a_1650_;
goto v___jp_1791_;
}
}
}
else
{
lean_dec(v___x_1815_);
v___y_1792_ = v_a_1645_;
v___y_1793_ = v_a_1646_;
v___y_1794_ = v_a_1647_;
v___y_1795_ = v_a_1648_;
v___y_1796_ = v_a_1649_;
v___y_1797_ = v_a_1650_;
goto v___jp_1791_;
}
}
v___jp_1791_:
{
lean_object* v___x_1798_; lean_object* v_rhs_1799_; 
v___x_1798_ = lean_unsigned_to_nat(3u);
v_rhs_1799_ = l_Lean_Syntax_getArg(v_decl_1644_, v___x_1798_);
lean_dec(v_decl_1644_);
if (v_reassignment_1643_ == 0)
{
lean_object* v___x_1800_; 
lean_dec(v_x_1790_);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1653_ = v___y_1792_;
v___y_1654_ = v_rhs_1799_;
v___y_1655_ = v___y_1797_;
v___y_1656_ = v___y_1796_;
v___y_1657_ = v___y_1795_;
v___y_1658_ = v___y_1794_;
v___y_1659_ = v___y_1793_;
v___y_1660_ = v___x_1800_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_mk_empty_array_with_capacity(v___x_1801_);
v___x_1803_ = lean_array_push(v___x_1802_, v_x_1790_);
v___y_1653_ = v___y_1792_;
v___y_1654_ = v_rhs_1799_;
v___y_1655_ = v___y_1797_;
v___y_1656_ = v___y_1796_;
v___y_1657_ = v___y_1795_;
v___y_1658_ = v___y_1794_;
v___y_1659_ = v___y_1793_;
v___y_1660_ = v___x_1803_;
goto v___jp_1652_;
}
}
}
v___jp_1652_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1654_);
v___x_1662_ = lean_box(0);
v___x_1663_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1660_, v___x_1661_, v___x_1662_, v___x_1662_, v___y_1653_, v___y_1659_, v___y_1658_, v___y_1657_, v___y_1656_, v___y_1655_);
return v___x_1663_;
}
v___jp_1664_:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___y_1667_);
if (lean_obj_tag(v___y_1665_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1668_, v___x_1675_, v___y_1666_, v___x_1676_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v___x_1677_;
}
else
{
lean_object* v_val_1678_; lean_object* v___x_1679_; 
v_val_1678_ = lean_ctor_get(v___y_1665_, 0);
lean_inc(v_val_1678_);
lean_dec_ref(v___y_1665_);
v___x_1679_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1668_, v___x_1675_, v___y_1666_, v_val_1678_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1939_, size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_b_1942_);
return v___x_1951_;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_array_uget_borrowed(v_as_1939_, v_i_1941_);
lean_inc(v_a_1952_);
v___x_1953_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1952_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; size_t v___x_1956_; size_t v___x_1957_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1953_);
v___x_1955_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1954_, v_b_1942_);
v___x_1956_ = ((size_t)1ULL);
v___x_1957_ = lean_usize_add(v_i_1941_, v___x_1956_);
v_i_1941_ = v___x_1957_;
v_b_1942_ = v___x_1955_;
goto _start;
}
else
{
lean_dec_ref(v_b_1942_);
return v___x_1953_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_1973_ = l_Lean_stringToMessageData(v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_1988_, lean_object* v_as_1989_, size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_b_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_a_2001_; uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1992_);
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; lean_object* v_a_2008_; uint8_t v___x_2009_; 
v___x_2007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2008_ = lean_array_uget_borrowed(v_as_1989_, v_i_1991_);
lean_inc(v_a_2008_);
v___x_2009_ = l_Lean_Syntax_isOfKind(v_a_2008_, v___x_2007_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_dec_ref(v___x_2010_);
v_a_2001_ = v_b_1992_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v_b_1992_);
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___y_2022_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_unsigned_to_nat(3u);
v___x_2039_ = l_Lean_Syntax_getArg(v_a_2008_, v___x_2019_);
v___x_2040_ = l_Lean_Syntax_getArgs(v___x_2039_);
lean_dec(v___x_2039_);
v___x_2041_ = lean_unsigned_to_nat(0u);
v___x_2042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2043_ = lean_array_get_size(v___x_2040_);
v___x_2044_ = lean_nat_dec_lt(v___x_2041_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_dec_ref(v___x_2040_);
v___y_2022_ = v___x_2042_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = lean_box(v___x_2009_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2042_);
v___x_2047_ = lean_nat_dec_le(v___x_2043_, v___x_2043_);
if (v___x_2047_ == 0)
{
if (v___x_2044_ == 0)
{
lean_dec_ref(v___x_2046_);
lean_dec_ref(v___x_2040_);
v___y_2022_ = v___x_2042_;
goto v___jp_2021_;
}
else
{
size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; lean_object* v_snd_2051_; 
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = lean_usize_of_nat(v___x_2043_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2009_, v___x_1988_, v___x_2040_, v___x_2048_, v___x_2049_, v___x_2046_);
lean_dec_ref(v___x_2040_);
v_snd_2051_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_snd_2051_);
lean_dec_ref(v___x_2050_);
v___y_2022_ = v_snd_2051_;
goto v___jp_2021_;
}
}
else
{
size_t v___x_2052_; size_t v___x_2053_; lean_object* v___x_2054_; lean_object* v_snd_2055_; 
v___x_2052_ = ((size_t)0ULL);
v___x_2053_ = lean_usize_of_nat(v___x_2043_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2009_, v___x_1988_, v___x_2040_, v___x_2052_, v___x_2053_, v___x_2046_);
lean_dec_ref(v___x_2040_);
v_snd_2055_ = lean_ctor_get(v___x_2054_, 1);
lean_inc(v_snd_2055_);
lean_dec_ref(v___x_2054_);
v___y_2022_ = v_snd_2055_;
goto v___jp_2021_;
}
}
v___jp_2021_:
{
size_t v_sz_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v_sz_2023_ = lean_array_size(v___y_2022_);
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2023_, v___x_2024_, v___y_2022_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_dec_ref(v___x_2026_);
v_a_2001_ = v_b_1992_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v_b_1992_);
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec_ref(v___x_2025_);
v___x_2035_ = l_Lean_Syntax_getArg(v_a_2008_, v___x_2020_);
v___x_2036_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2035_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2036_);
v___x_2038_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_1992_, v_a_2037_);
v_a_2001_ = v___x_2038_;
goto v___jp_2000_;
}
else
{
lean_dec_ref(v_b_1992_);
return v___x_2036_;
}
}
}
}
}
v___jp_2000_:
{
size_t v___x_2002_; size_t v___x_2003_; 
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1991_, v___x_2002_);
v_i_1991_ = v___x_2003_;
v_b_1992_ = v_a_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2056_, size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_b_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_a_2068_; uint8_t v___x_2072_; 
v___x_2072_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_b_2059_);
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v_a_2075_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2074_ = lean_unsigned_to_nat(0u);
v_a_2075_ = lean_array_uget_borrowed(v_as_2056_, v_i_2058_);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2075_);
v___x_2089_ = l_Lean_Syntax_isOfKind(v_a_2075_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2075_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v_a_2075_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2093_ = lean_box(0);
lean_inc(v_a_2075_);
v___x_2094_ = l_Lean_Syntax_formatStx(v_a_2075_, v___x_2093_, v___x_2091_);
v___x_2095_ = l_Std_Format_defWidth;
v___x_2096_ = l_Std_Format_pretty(v___x_2094_, v___x_2095_, v___x_2074_, v___x_2074_);
v___x_2097_ = l_Lean_stringToMessageData(v___x_2096_);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2092_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2098_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_dec_ref(v___x_2099_);
v_a_2068_ = v_b_2059_;
goto v___jp_2067_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_b_2059_);
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = l_Lean_Syntax_getArg(v_a_2075_, v___x_2108_);
v___x_2110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2109_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v___x_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec(v___x_2109_);
v___x_2112_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2113_ = lean_box(0);
lean_inc(v_a_2075_);
v___x_2114_ = l_Lean_Syntax_formatStx(v_a_2075_, v___x_2113_, v___x_2111_);
v___x_2115_ = l_Std_Format_defWidth;
v___x_2116_ = l_Std_Format_pretty(v___x_2114_, v___x_2115_, v___x_2074_, v___x_2074_);
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2112_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2118_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_dec_ref(v___x_2119_);
v_a_2068_ = v_b_2059_;
goto v___jp_2067_;
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_b_2059_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2128_ = l_Lean_Syntax_getArg(v___x_2109_, v___x_2074_);
lean_dec(v___x_2109_);
v___x_2129_ = l_Lean_Syntax_getArgs(v___x_2128_);
lean_dec(v___x_2128_);
v_sz_2130_ = lean_array_size(v___x_2129_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2089_, v___x_2129_, v_sz_2130_, v___x_2131_, v_b_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec_ref(v___x_2129_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
v_a_2068_ = v_a_2133_;
goto v___jp_2067_;
}
else
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2134_ = lean_unsigned_to_nat(2u);
v___x_2135_ = l_Lean_Syntax_getArg(v_a_2075_, v___x_2134_);
v___x_2136_ = l_Lean_Syntax_isNone(v___x_2135_);
if (v___x_2136_ == 0)
{
uint8_t v___x_2137_; 
v___x_2137_ = l_Lean_Syntax_matchesNull(v___x_2135_, v___x_2134_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2139_ = lean_box(0);
lean_inc(v_a_2075_);
v___x_2140_ = l_Lean_Syntax_formatStx(v_a_2075_, v___x_2139_, v___x_2137_);
v___x_2141_ = l_Std_Format_defWidth;
v___x_2142_ = l_Std_Format_pretty(v___x_2140_, v___x_2141_, v___x_2074_, v___x_2074_);
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2138_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2144_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_dec_ref(v___x_2145_);
v_a_2068_ = v_b_2059_;
goto v___jp_2067_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v_b_2059_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
v___y_2077_ = v___y_2060_;
v___y_2078_ = v___y_2061_;
v___y_2079_ = v___y_2062_;
v___y_2080_ = v___y_2063_;
v___y_2081_ = v___y_2064_;
v___y_2082_ = v___y_2065_;
goto v___jp_2076_;
}
}
else
{
lean_dec(v___x_2135_);
v___y_2077_ = v___y_2060_;
v___y_2078_ = v___y_2061_;
v___y_2079_ = v___y_2062_;
v___y_2080_ = v___y_2063_;
v___y_2081_ = v___y_2064_;
v___y_2082_ = v___y_2065_;
goto v___jp_2076_;
}
}
v___jp_2076_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_unsigned_to_nat(4u);
v___x_2084_ = l_Lean_Syntax_getArg(v_a_2075_, v___x_2083_);
v___x_2085_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2084_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2086_, v_b_2059_);
v_a_2068_ = v___x_2087_;
goto v___jp_2067_;
}
else
{
lean_dec_ref(v_b_2059_);
return v___x_2085_;
}
}
}
v___jp_2067_:
{
size_t v___x_2069_; size_t v___x_2070_; 
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_add(v_i_2058_, v___x_2069_);
v_i_2058_ = v___x_2070_;
v_b_2059_ = v_a_2068_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2154_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
else
{
lean_object* v_val_2164_; lean_object* v___x_2165_; 
v_val_2164_ = lean_ctor_get(v_stx_x3f_2154_, 0);
lean_inc(v_val_2164_);
lean_dec_ref(v_stx_x3f_2154_);
v___x_2165_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2164_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2172_, lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_a_2185_; uint8_t v___x_2189_; 
v___x_2189_ = lean_usize_dec_lt(v_i_2175_, v_sz_2174_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_b_2176_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; lean_object* v_a_2192_; uint8_t v___x_2193_; 
v___x_2191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2192_ = lean_array_uget_borrowed(v_as_2173_, v_i_2175_);
lean_inc(v_a_2192_);
v___x_2193_ = l_Lean_Syntax_isOfKind(v_a_2192_, v___x_2191_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_dec_ref(v___x_2194_);
v_a_2185_ = v_b_2176_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_b_2176_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___y_2206_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_unsigned_to_nat(3u);
v___x_2223_ = l_Lean_Syntax_getArg(v_a_2192_, v___x_2203_);
v___x_2224_ = l_Lean_Syntax_getArgs(v___x_2223_);
lean_dec(v___x_2223_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2227_ = lean_array_get_size(v___x_2224_);
v___x_2228_ = lean_nat_dec_lt(v___x_2225_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v___x_2224_);
v___y_2206_ = v___x_2226_;
goto v___jp_2205_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2229_ = lean_box(v___x_2193_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2226_);
v___x_2231_ = lean_nat_dec_le(v___x_2227_, v___x_2227_);
if (v___x_2231_ == 0)
{
if (v___x_2228_ == 0)
{
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2224_);
v___y_2206_ = v___x_2226_;
goto v___jp_2205_;
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v_snd_2235_; 
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2227_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2193_, v___x_2172_, v___x_2224_, v___x_2232_, v___x_2233_, v___x_2230_);
lean_dec_ref(v___x_2224_);
v_snd_2235_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_snd_2235_);
lean_dec_ref(v___x_2234_);
v___y_2206_ = v_snd_2235_;
goto v___jp_2205_;
}
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; lean_object* v_snd_2239_; 
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = lean_usize_of_nat(v___x_2227_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2193_, v___x_2172_, v___x_2224_, v___x_2236_, v___x_2237_, v___x_2230_);
lean_dec_ref(v___x_2224_);
v_snd_2239_ = lean_ctor_get(v___x_2238_, 1);
lean_inc(v_snd_2239_);
lean_dec_ref(v___x_2238_);
v___y_2206_ = v_snd_2239_;
goto v___jp_2205_;
}
}
v___jp_2205_:
{
size_t v_sz_2207_; size_t v___x_2208_; lean_object* v___x_2209_; 
v_sz_2207_ = lean_array_size(v___y_2206_);
v___x_2208_ = ((size_t)0ULL);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2207_, v___x_2208_, v___y_2206_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_dec_ref(v___x_2210_);
v_a_2185_ = v_b_2176_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v_b_2176_);
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec_ref(v___x_2209_);
v___x_2219_ = l_Lean_Syntax_getArg(v_a_2192_, v___x_2204_);
v___x_2220_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2219_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2176_, v_a_2221_);
v_a_2185_ = v___x_2222_;
goto v___jp_2184_;
}
else
{
lean_dec_ref(v_b_2176_);
return v___x_2220_;
}
}
}
}
}
v___jp_2184_:
{
size_t v___x_2186_; size_t v___x_2187_; 
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2175_, v___x_2186_);
v_i_2175_ = v___x_2187_;
v_b_2176_ = v_a_2185_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2276_ = l_Lean_NameSet_empty;
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = 0;
v___x_2279_ = 1;
v___x_2280_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2280_, 0, v___x_2277_);
lean_ctor_set(v___x_2280_, 1, v___x_2276_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*2, v___x_2279_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*2 + 1, v___x_2278_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*2 + 2, v___x_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2324_; lean_object* v_bodyInfo_2325_; lean_object* v___y_2329_; lean_object* v_bodyInfo_2330_; lean_object* v___x_2333_; lean_object* v_env_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2333_ = lean_st_ref_get(v_a_2287_);
v_env_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_ref(v_env_2334_);
lean_dec(v___x_2333_);
lean_inc(v_stx_2281_);
v___x_2335_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2335_, 0, v_env_2334_);
lean_closure_set(v___x_2335_, 1, v_stx_2281_);
v___x_2336_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2335_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_4141_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_4141_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_4141_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
if (lean_obj_tag(v_a_2337_) == 1)
{
lean_object* v_val_2341_; lean_object* v_snd_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_del_object(v___x_2339_);
lean_dec(v_stx_2281_);
v_val_2341_ = lean_ctor_get(v_a_2337_, 0);
lean_inc(v_val_2341_);
lean_dec_ref(v_a_2337_);
v_snd_2342_ = lean_ctor_get(v_val_2341_, 1);
lean_inc(v_snd_2342_);
lean_dec(v_val_2341_);
v___x_2343_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2343_, 0, lean_box(0));
lean_closure_set(v___x_2343_, 1, v_snd_2342_);
v___x_2344_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2343_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref(v___x_2344_);
v_stx_2281_ = v_a_2345_;
goto _start;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_a_2347_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2344_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2344_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___x_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; 
lean_dec(v_a_2337_);
v___x_2416_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
lean_inc(v_stx_2281_);
v___x_2417_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2416_);
v___x_2418_ = 1;
if (v___x_2417_ == 0)
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2281_);
v___x_2420_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2281_);
v___x_2422_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2281_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2281_);
v___x_2426_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2281_);
v___x_2428_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
lean_del_object(v___x_2339_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2281_);
v___x_2430_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2281_);
v___x_2432_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; uint8_t v___x_2434_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; 
v___x_2433_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2281_);
v___x_2434_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2281_);
v___x_2446_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2281_);
v___x_2448_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2281_);
v___x_2450_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2281_);
v___x_2452_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2281_);
v___x_2454_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2281_);
v___x_2456_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2281_);
v___x_2458_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2281_);
v___x_2460_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2281_);
v___x_2462_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2281_);
v___x_2464_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2281_);
v___x_2466_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51));
lean_inc(v_stx_2281_);
v___x_2468_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53));
lean_inc(v_stx_2281_);
v___x_2470_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55));
lean_inc(v_stx_2281_);
v___x_2472_ = l_Lean_Syntax_isOfKind(v_stx_2281_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v_env_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2473_ = lean_st_ref_get(v_a_2287_);
v_env_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_env_2474_);
lean_dec(v___x_2473_);
v___x_2475_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2476_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2477_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2475_, v_env_2474_, v___x_2476_);
v___x_2478_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2479_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2477_, v___x_2478_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2510_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2510_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2510_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_fst_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2508_; 
v_fst_2484_ = lean_ctor_get(v_a_2480_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_a_2480_);
if (v_isSharedCheck_2508_ == 0)
{
lean_object* v_unused_2509_; 
v_unused_2509_ = lean_ctor_get(v_a_2480_, 1);
lean_dec(v_unused_2509_);
v___x_2486_ = v_a_2480_;
v_isShared_2487_ = v_isSharedCheck_2508_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_fst_2484_);
lean_dec(v_a_2480_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2508_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_fst_2484_) == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
lean_del_object(v___x_2482_);
v___x_2488_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2489_ = l_Lean_MessageData_ofName(v___x_2476_);
lean_inc_ref(v___x_2489_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 7);
lean_ctor_set(v___x_2486_, 1, v___x_2489_);
lean_ctor_set(v___x_2486_, 0, v___x_2488_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2492_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2495_ = l_Lean_indentD(v___x_2494_);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2493_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2489_);
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2501_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2502_;
}
}
else
{
lean_object* v_val_2504_; lean_object* v___x_2506_; 
lean_del_object(v___x_2486_);
lean_dec(v___x_2476_);
lean_dec(v_stx_2281_);
v_val_2504_ = lean_ctor_get(v_fst_2484_, 0);
lean_inc(v_val_2504_);
lean_dec_ref(v_fst_2484_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v_val_2504_);
v___x_2506_ = v___x_2482_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_val_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v___x_2476_);
lean_dec(v_stx_2281_);
v_a_2511_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2479_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2479_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
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
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___y_2523_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_unsigned_to_nat(5u);
v___x_2521_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2520_);
v___x_2532_ = lean_unsigned_to_nat(6u);
v___x_2533_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2532_);
lean_dec(v_stx_2281_);
v___x_2534_ = l_Lean_Syntax_getOptional_x3f(v___x_2533_);
lean_dec(v___x_2533_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_box(0);
v___y_2523_ = v___x_2535_;
goto v___jp_2522_;
}
else
{
lean_object* v_val_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_val_2536_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2534_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_val_2536_);
lean_dec(v___x_2534_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_val_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
v___y_2523_ = v___x_2541_;
goto v___jp_2522_;
}
}
}
v___jp_2522_:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2521_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2524_) == 0)
{
if (lean_obj_tag(v___y_2523_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = l_Lean_NameSet_empty;
v___x_2527_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2527_, 0, v___x_2519_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2, v___x_2470_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2 + 1, v___x_2470_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2 + 2, v___x_2470_);
v___y_2329_ = v_a_2525_;
v_bodyInfo_2330_ = v___x_2527_;
goto v___jp_2328_;
}
else
{
lean_object* v_a_2528_; lean_object* v_val_2529_; lean_object* v___x_2530_; 
v_a_2528_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v___x_2524_);
v_val_2529_ = lean_ctor_get(v___y_2523_, 0);
lean_inc(v_val_2529_);
lean_dec_ref(v___y_2523_);
v___x_2530_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2529_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref(v___x_2530_);
v___y_2329_ = v_a_2528_;
v_bodyInfo_2330_ = v_a_2531_;
goto v___jp_2328_;
}
else
{
lean_dec(v_a_2528_);
return v___x_2530_;
}
}
}
else
{
lean_dec(v___y_2523_);
return v___x_2524_;
}
}
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___y_2548_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_unsigned_to_nat(5u);
v___x_2546_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2545_);
v___x_2557_ = lean_unsigned_to_nat(6u);
v___x_2558_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2557_);
lean_dec(v_stx_2281_);
v___x_2559_ = l_Lean_Syntax_getOptional_x3f(v___x_2558_);
lean_dec(v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_box(0);
v___y_2548_ = v___x_2560_;
goto v___jp_2547_;
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
v_val_2561_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2559_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_val_2561_);
lean_dec(v___x_2559_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_val_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
v___y_2548_ = v___x_2566_;
goto v___jp_2547_;
}
}
}
v___jp_2547_:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2546_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2549_) == 0)
{
if (lean_obj_tag(v___y_2548_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref(v___x_2549_);
v___x_2551_ = l_Lean_NameSet_empty;
v___x_2552_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2552_, 0, v___x_2544_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*2, v___x_2468_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*2 + 1, v___x_2468_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*2 + 2, v___x_2468_);
v___y_2324_ = v_a_2550_;
v_bodyInfo_2325_ = v___x_2552_;
goto v___jp_2323_;
}
else
{
lean_object* v_a_2553_; lean_object* v_val_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2549_);
v_val_2554_ = lean_ctor_get(v___y_2548_, 0);
lean_inc(v_val_2554_);
lean_dec_ref(v___y_2548_);
v___x_2555_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2554_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2555_);
v___y_2324_ = v_a_2553_;
v_bodyInfo_2325_ = v_a_2556_;
goto v___jp_2323_;
}
else
{
lean_dec(v_a_2553_);
return v___x_2555_;
}
}
}
else
{
lean_dec(v___y_2548_);
return v___x_2549_;
}
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v___x_2569_ = lean_unsigned_to_nat(0u);
v___x_2570_ = lean_unsigned_to_nat(1u);
v___x_2784_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2570_);
v___x_2785_ = l_Lean_Syntax_isNone(v___x_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = lean_unsigned_to_nat(5u);
v___x_2787_ = l_Lean_Syntax_matchesNull(v___x_2784_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v_env_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = lean_st_ref_get(v_a_2287_);
v_env_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_ref(v_env_2789_);
lean_dec(v___x_2788_);
v___x_2790_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2791_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2792_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2790_, v_env_2789_, v___x_2791_);
v___x_2793_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2794_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2792_, v___x_2793_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2825_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2825_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2825_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_fst_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2823_; 
v_fst_2799_ = lean_ctor_get(v_a_2795_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_a_2795_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_a_2795_, 1);
lean_dec(v_unused_2824_);
v___x_2801_ = v_a_2795_;
v_isShared_2802_ = v_isSharedCheck_2823_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_fst_2799_);
lean_dec(v_a_2795_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2823_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
if (lean_obj_tag(v_fst_2799_) == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_del_object(v___x_2797_);
v___x_2803_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2804_ = l_Lean_MessageData_ofName(v___x_2791_);
lean_inc_ref(v___x_2804_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 7);
lean_ctor_set(v___x_2801_, 1, v___x_2804_);
lean_ctor_set(v___x_2801_, 0, v___x_2803_);
v___x_2806_ = v___x_2801_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2807_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2810_ = l_Lean_indentD(v___x_2809_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2808_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2804_);
v___x_2815_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2816_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2817_;
}
}
else
{
lean_object* v_val_2819_; lean_object* v___x_2821_; 
lean_del_object(v___x_2801_);
lean_dec(v___x_2791_);
lean_dec(v_stx_2281_);
v_val_2819_ = lean_ctor_get(v_fst_2799_, 0);
lean_inc(v_val_2819_);
lean_dec_ref(v_fst_2799_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_val_2819_);
v___x_2821_ = v___x_2797_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_val_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___x_2791_);
lean_dec(v_stx_2281_);
v_a_2826_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2794_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2794_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
v___y_2572_ = v_a_2282_;
v___y_2573_ = v_a_2283_;
v___y_2574_ = v_a_2284_;
v___y_2575_ = v_a_2285_;
v___y_2576_ = v_a_2286_;
v___y_2577_ = v_a_2287_;
goto v___jp_2571_;
}
}
else
{
lean_dec(v___x_2784_);
v___y_2572_ = v_a_2282_;
v___y_2573_ = v_a_2283_;
v___y_2574_ = v_a_2284_;
v___y_2575_ = v_a_2285_;
v___y_2576_ = v_a_2286_;
v___y_2577_ = v_a_2287_;
goto v___jp_2571_;
}
v___jp_2571_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2578_ = lean_unsigned_to_nat(4u);
v___x_2579_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57));
lean_inc(v___x_2579_);
v___x_2581_ = l_Lean_Syntax_isOfKind(v___x_2579_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v_env_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec(v___x_2579_);
v___x_2582_ = lean_st_ref_get(v___y_2577_);
v_env_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc_ref(v_env_2583_);
lean_dec(v___x_2582_);
v___x_2584_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2585_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2586_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2584_, v_env_2583_, v___x_2585_);
v___x_2587_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2588_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2586_, v___x_2587_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2619_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2619_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2619_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_fst_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2617_; 
v_fst_2593_ = lean_ctor_get(v_a_2589_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2589_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v_a_2589_, 1);
lean_dec(v_unused_2618_);
v___x_2595_ = v_a_2589_;
v_isShared_2596_ = v_isSharedCheck_2617_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_fst_2593_);
lean_dec(v_a_2589_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2617_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
if (lean_obj_tag(v_fst_2593_) == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_del_object(v___x_2591_);
v___x_2597_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2598_ = l_Lean_MessageData_ofName(v___x_2585_);
lean_inc_ref(v___x_2598_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 7);
lean_ctor_set(v___x_2595_, 1, v___x_2598_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2601_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2604_ = l_Lean_indentD(v___x_2603_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2602_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2598_);
v___x_2609_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2610_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2611_;
}
}
else
{
lean_object* v_val_2613_; lean_object* v___x_2615_; 
lean_del_object(v___x_2595_);
lean_dec(v___x_2585_);
lean_dec(v_stx_2281_);
v_val_2613_ = lean_ctor_get(v_fst_2593_, 0);
lean_inc(v_val_2613_);
lean_dec_ref(v_fst_2593_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_val_2613_);
v___x_2615_ = v___x_2591_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_val_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v___x_2585_);
lean_dec(v_stx_2281_);
v_a_2620_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2588_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2588_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; size_t v_sz_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2628_ = l_Lean_Syntax_getArg(v___x_2579_, v___x_2569_);
v___x_2629_ = l_Lean_Syntax_getArgs(v___x_2628_);
lean_dec(v___x_2628_);
v_sz_2630_ = lean_array_size(v___x_2629_);
v___x_2631_ = ((size_t)0ULL);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2630_, v___x_2631_, v___x_2629_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; lean_object* v_env_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec(v___x_2579_);
v___x_2633_ = lean_st_ref_get(v___y_2577_);
v_env_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc_ref(v_env_2634_);
lean_dec(v___x_2633_);
v___x_2635_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2636_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2637_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2635_, v_env_2634_, v___x_2636_);
v___x_2638_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2639_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2637_, v___x_2638_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2670_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2670_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2670_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_fst_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2668_; 
v_fst_2644_ = lean_ctor_get(v_a_2640_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2640_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; 
v_unused_2669_ = lean_ctor_get(v_a_2640_, 1);
lean_dec(v_unused_2669_);
v___x_2646_ = v_a_2640_;
v_isShared_2647_ = v_isSharedCheck_2668_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_fst_2644_);
lean_dec(v_a_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2668_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
if (lean_obj_tag(v_fst_2644_) == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_del_object(v___x_2642_);
v___x_2648_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2649_ = l_Lean_MessageData_ofName(v___x_2636_);
lean_inc_ref(v___x_2649_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 7);
lean_ctor_set(v___x_2646_, 1, v___x_2649_);
lean_ctor_set(v___x_2646_, 0, v___x_2648_);
v___x_2651_ = v___x_2646_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2652_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2655_ = l_Lean_indentD(v___x_2654_);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___x_2649_);
v___x_2660_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2661_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2662_;
}
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2666_; 
lean_del_object(v___x_2646_);
lean_dec(v___x_2636_);
lean_dec(v_stx_2281_);
v_val_2664_ = lean_ctor_get(v_fst_2644_, 0);
lean_inc(v_val_2664_);
lean_dec_ref(v_fst_2644_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_val_2664_);
v___x_2666_ = v___x_2642_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_val_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v___x_2636_);
lean_dec(v_stx_2281_);
v_a_2671_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2639_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2639_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_val_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v_val_2679_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2679_);
lean_dec_ref(v___x_2632_);
v___x_2680_ = l_Lean_Syntax_getArg(v___x_2579_, v___x_2570_);
lean_dec(v___x_2579_);
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59));
lean_inc(v___x_2680_);
v___x_2682_ = l_Lean_Syntax_isOfKind(v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v_env_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec(v___x_2680_);
lean_dec(v_val_2679_);
v___x_2683_ = lean_st_ref_get(v___y_2577_);
v_env_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc_ref(v_env_2684_);
lean_dec(v___x_2683_);
v___x_2685_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2686_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2687_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2685_, v_env_2684_, v___x_2686_);
v___x_2688_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2689_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2687_, v___x_2688_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2720_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2720_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2720_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_fst_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2718_; 
v_fst_2694_ = lean_ctor_get(v_a_2690_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_a_2690_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_a_2690_, 1);
lean_dec(v_unused_2719_);
v___x_2696_ = v_a_2690_;
v_isShared_2697_ = v_isSharedCheck_2718_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_fst_2694_);
lean_dec(v_a_2690_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2718_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
if (lean_obj_tag(v_fst_2694_) == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_del_object(v___x_2692_);
v___x_2698_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2699_ = l_Lean_MessageData_ofName(v___x_2686_);
lean_inc_ref(v___x_2699_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 7);
lean_ctor_set(v___x_2696_, 1, v___x_2699_);
lean_ctor_set(v___x_2696_, 0, v___x_2698_);
v___x_2701_ = v___x_2696_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2702_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2705_ = l_Lean_indentD(v___x_2704_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2703_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2699_);
v___x_2710_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2711_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2712_;
}
}
else
{
lean_object* v_val_2714_; lean_object* v___x_2716_; 
lean_del_object(v___x_2696_);
lean_dec(v___x_2686_);
lean_dec(v_stx_2281_);
v_val_2714_ = lean_ctor_get(v_fst_2694_, 0);
lean_inc(v_val_2714_);
lean_dec_ref(v_fst_2694_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_val_2714_);
v___x_2716_ = v___x_2692_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_val_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v___x_2686_);
lean_dec(v_stx_2281_);
v_a_2721_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2689_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2689_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = l_Lean_Syntax_getArg(v___x_2680_, v___x_2570_);
v___x_2730_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61));
v___x_2731_ = l_Lean_Syntax_isOfKind(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v_env_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_dec(v___x_2680_);
lean_dec(v_val_2679_);
v___x_2732_ = lean_st_ref_get(v___y_2577_);
v_env_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc_ref(v_env_2733_);
lean_dec(v___x_2732_);
v___x_2734_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2735_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2736_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2734_, v_env_2733_, v___x_2735_);
v___x_2737_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2738_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2736_, v___x_2737_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2769_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2769_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2769_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_fst_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2767_; 
v_fst_2743_ = lean_ctor_get(v_a_2739_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_a_2739_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v_a_2739_, 1);
lean_dec(v_unused_2768_);
v___x_2745_ = v_a_2739_;
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_fst_2743_);
lean_dec(v_a_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
if (lean_obj_tag(v_fst_2743_) == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
lean_del_object(v___x_2741_);
v___x_2747_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2748_ = l_Lean_MessageData_ofName(v___x_2735_);
lean_inc_ref(v___x_2748_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 7);
lean_ctor_set(v___x_2745_, 1, v___x_2748_);
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2750_ = v___x_2745_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2751_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2754_ = l_Lean_indentD(v___x_2753_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2752_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v___x_2748_);
v___x_2759_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2760_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2761_;
}
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2765_; 
lean_del_object(v___x_2745_);
lean_dec(v___x_2735_);
lean_dec(v_stx_2281_);
v_val_2763_ = lean_ctor_get(v_fst_2743_, 0);
lean_inc(v_val_2763_);
lean_dec_ref(v_fst_2743_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v_val_2763_);
v___x_2765_ = v___x_2741_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_val_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v___x_2735_);
lean_dec(v_stx_2281_);
v_a_2770_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2738_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2738_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec(v_stx_2281_);
v___x_2778_ = lean_unsigned_to_nat(3u);
v___x_2779_ = l_Lean_Syntax_getArg(v___x_2680_, v___x_2778_);
lean_dec(v___x_2680_);
v___x_2780_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2779_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; size_t v_sz_2782_; lean_object* v___x_2783_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___x_2780_);
v_sz_2782_ = lean_array_size(v_val_2679_);
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2679_, v_sz_2782_, v___x_2631_, v_a_2781_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v_val_2679_);
return v___x_2783_;
}
else
{
lean_dec(v_val_2679_);
return v___x_2780_;
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
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec(v_stx_2281_);
v___x_2834_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v_stx_2281_);
v___x_2836_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v_stx_2281_);
v___x_2838_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; size_t v_sz_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2840_ = lean_unsigned_to_nat(2u);
v___x_2841_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2840_);
v___x_2842_ = l_Lean_Syntax_getArgs(v___x_2841_);
lean_dec(v___x_2841_);
v_sz_2843_ = lean_array_size(v___x_2842_);
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_2843_, v___x_2844_, v___x_2842_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v___x_2846_; lean_object* v_env_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2846_ = lean_st_ref_get(v_a_2287_);
v_env_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_env_2847_);
lean_dec(v___x_2846_);
v___x_2848_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2849_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2850_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2848_, v_env_2847_, v___x_2849_);
v___x_2851_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2852_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2850_, v___x_2851_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2883_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2883_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2883_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_fst_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2881_; 
v_fst_2857_ = lean_ctor_get(v_a_2853_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v_a_2853_, 1);
lean_dec(v_unused_2882_);
v___x_2859_ = v_a_2853_;
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_fst_2857_);
lean_dec(v_a_2853_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
if (lean_obj_tag(v_fst_2857_) == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_del_object(v___x_2855_);
v___x_2861_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2862_ = l_Lean_MessageData_ofName(v___x_2849_);
lean_inc_ref(v___x_2862_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 7);
lean_ctor_set(v___x_2859_, 1, v___x_2862_);
lean_ctor_set(v___x_2859_, 0, v___x_2861_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2865_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2868_ = l_Lean_indentD(v___x_2867_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2866_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2862_);
v___x_2873_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2874_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2875_;
}
}
else
{
lean_object* v_val_2877_; lean_object* v___x_2879_; 
lean_del_object(v___x_2859_);
lean_dec(v___x_2849_);
lean_dec(v_stx_2281_);
v_val_2877_ = lean_ctor_get(v_fst_2857_, 0);
lean_inc(v_val_2877_);
lean_dec_ref(v_fst_2857_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_val_2877_);
v___x_2879_ = v___x_2855_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_val_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___x_2849_);
lean_dec(v_stx_2281_);
v_a_2884_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2852_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2852_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_val_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_3026_; 
v_val_2892_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2894_ = v___x_2845_;
v_isShared_2895_ = v_isSharedCheck_3026_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_val_2892_);
lean_dec(v___x_2845_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_3026_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_finSeq_x3f_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2896_);
v___x_2921_ = lean_unsigned_to_nat(3u);
v___x_2922_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2921_);
v___x_2923_ = l_Lean_Syntax_isNone(v___x_2922_);
if (v___x_2923_ == 0)
{
uint8_t v___x_2924_; 
lean_inc(v___x_2922_);
v___x_2924_ = l_Lean_Syntax_matchesNull(v___x_2922_, v___x_2896_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v_env_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v___x_2922_);
lean_dec(v___x_2897_);
lean_del_object(v___x_2894_);
lean_dec(v_val_2892_);
v___x_2925_ = lean_st_ref_get(v_a_2287_);
v_env_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc_ref(v_env_2926_);
lean_dec(v___x_2925_);
v___x_2927_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2928_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2929_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2927_, v_env_2926_, v___x_2928_);
v___x_2930_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2931_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2929_, v___x_2930_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2962_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2962_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2962_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v_fst_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2960_; 
v_fst_2936_ = lean_ctor_get(v_a_2932_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2932_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_a_2932_, 1);
lean_dec(v_unused_2961_);
v___x_2938_ = v_a_2932_;
v_isShared_2939_ = v_isSharedCheck_2960_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_fst_2936_);
lean_dec(v_a_2932_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2960_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
if (lean_obj_tag(v_fst_2936_) == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
lean_del_object(v___x_2934_);
v___x_2940_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2941_ = l_Lean_MessageData_ofName(v___x_2928_);
lean_inc_ref(v___x_2941_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set_tag(v___x_2938_, 7);
lean_ctor_set(v___x_2938_, 1, v___x_2941_);
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2943_ = v___x_2938_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2944_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2947_ = l_Lean_indentD(v___x_2946_);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2945_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2941_);
v___x_2952_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2953_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2954_;
}
}
else
{
lean_object* v_val_2956_; lean_object* v___x_2958_; 
lean_del_object(v___x_2938_);
lean_dec(v___x_2928_);
lean_dec(v_stx_2281_);
v_val_2956_ = lean_ctor_get(v_fst_2936_, 0);
lean_inc(v_val_2956_);
lean_dec_ref(v_fst_2936_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v_val_2956_);
v___x_2958_ = v___x_2934_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_val_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v___x_2928_);
lean_dec(v_stx_2281_);
v_a_2963_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2931_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2931_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = l_Lean_Syntax_getArg(v___x_2922_, v___x_2971_);
lean_dec(v___x_2922_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
lean_inc(v___x_2972_);
v___x_2974_ = l_Lean_Syntax_isOfKind(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v_env_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v___x_2972_);
lean_dec(v___x_2897_);
lean_del_object(v___x_2894_);
lean_dec(v_val_2892_);
v___x_2975_ = lean_st_ref_get(v_a_2287_);
v_env_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc_ref(v_env_2976_);
lean_dec(v___x_2975_);
v___x_2977_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2978_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2979_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2977_, v_env_2976_, v___x_2978_);
v___x_2980_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2981_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2979_, v___x_2980_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3012_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2984_ = v___x_2981_;
v_isShared_2985_ = v_isSharedCheck_3012_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3012_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v_fst_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3010_; 
v_fst_2986_ = lean_ctor_get(v_a_2982_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_a_2982_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v_a_2982_, 1);
lean_dec(v_unused_3011_);
v___x_2988_ = v_a_2982_;
v_isShared_2989_ = v_isSharedCheck_3010_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_fst_2986_);
lean_dec(v_a_2982_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3010_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
if (lean_obj_tag(v_fst_2986_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_del_object(v___x_2984_);
v___x_2990_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2991_ = l_Lean_MessageData_ofName(v___x_2978_);
lean_inc_ref(v___x_2991_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 7);
lean_ctor_set(v___x_2988_, 1, v___x_2991_);
lean_ctor_set(v___x_2988_, 0, v___x_2990_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2994_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2997_ = l_Lean_indentD(v___x_2996_);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2995_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2991_);
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3003_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3004_;
}
}
else
{
lean_object* v_val_3006_; lean_object* v___x_3008_; 
lean_del_object(v___x_2988_);
lean_dec(v___x_2978_);
lean_dec(v_stx_2281_);
v_val_3006_ = lean_ctor_get(v_fst_2986_, 0);
lean_inc(v_val_3006_);
lean_dec_ref(v_fst_2986_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v_val_3006_);
v___x_3008_ = v___x_2984_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_val_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v___x_2978_);
lean_dec(v_stx_2281_);
v_a_3013_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2981_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2981_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_dec(v_stx_2281_);
v___x_3021_ = l_Lean_Syntax_getArg(v___x_2972_, v___x_2896_);
lean_dec(v___x_2972_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_3021_);
v___x_3023_ = v___x_2894_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
v_finSeq_x3f_2899_ = v___x_3023_;
v___y_2900_ = v_a_2282_;
v___y_2901_ = v_a_2283_;
v___y_2902_ = v_a_2284_;
v___y_2903_ = v_a_2285_;
v___y_2904_ = v_a_2286_;
v___y_2905_ = v_a_2287_;
goto v___jp_2898_;
}
}
}
}
else
{
lean_object* v___x_3025_; 
lean_dec(v___x_2922_);
lean_del_object(v___x_2894_);
lean_dec(v_stx_2281_);
v___x_3025_ = lean_box(0);
v_finSeq_x3f_2899_ = v___x_3025_;
v___y_2900_ = v_a_2282_;
v___y_2901_ = v_a_2283_;
v___y_2902_ = v_a_2284_;
v___y_2903_ = v_a_2285_;
v___y_2904_ = v_a_2286_;
v___y_2905_ = v_a_2287_;
goto v___jp_2898_;
}
v___jp_2898_:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2897_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; size_t v_sz_2908_; lean_object* v___x_2909_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2906_);
v_sz_2908_ = lean_array_size(v_val_2892_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_2892_, v_sz_2908_, v___x_2844_, v_a_2907_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v_val_2892_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_2910_, v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_dec(v_a_2910_);
return v___x_2911_;
}
}
else
{
lean_dec(v_finSeq_x3f_2899_);
return v___x_2909_;
}
}
else
{
lean_dec(v_finSeq_x3f_2899_);
lean_dec(v_val_2892_);
return v___x_2906_;
}
}
}
}
}
}
else
{
lean_object* v___x_3027_; lean_object* v___y_3029_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3027_ = lean_unsigned_to_nat(1u);
v___x_3100_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3027_);
v___x_3101_ = l_Lean_Syntax_getArgs(v___x_3100_);
lean_dec(v___x_3100_);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3104_ = lean_array_get_size(v___x_3101_);
v___x_3105_ = lean_nat_dec_lt(v___x_3102_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_dec_ref(v___x_3101_);
v___y_3029_ = v___x_3103_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_box(v___x_2458_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3103_);
v___x_3108_ = lean_nat_dec_le(v___x_3104_, v___x_3104_);
if (v___x_3108_ == 0)
{
if (v___x_3105_ == 0)
{
lean_dec_ref(v___x_3107_);
lean_dec_ref(v___x_3101_);
v___y_3029_ = v___x_3103_;
goto v___jp_3028_;
}
else
{
size_t v___x_3109_; size_t v___x_3110_; lean_object* v___x_3111_; lean_object* v_snd_3112_; 
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = lean_usize_of_nat(v___x_3104_);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2458_, v___x_2456_, v___x_3101_, v___x_3109_, v___x_3110_, v___x_3107_);
lean_dec_ref(v___x_3101_);
v_snd_3112_ = lean_ctor_get(v___x_3111_, 1);
lean_inc(v_snd_3112_);
lean_dec_ref(v___x_3111_);
v___y_3029_ = v_snd_3112_;
goto v___jp_3028_;
}
}
else
{
size_t v___x_3113_; size_t v___x_3114_; lean_object* v___x_3115_; lean_object* v_snd_3116_; 
v___x_3113_ = ((size_t)0ULL);
v___x_3114_ = lean_usize_of_nat(v___x_3104_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2458_, v___x_2456_, v___x_3101_, v___x_3113_, v___x_3114_, v___x_3107_);
lean_dec_ref(v___x_3101_);
v_snd_3116_ = lean_ctor_get(v___x_3115_, 1);
lean_inc(v_snd_3116_);
lean_dec_ref(v___x_3115_);
v___y_3029_ = v_snd_3116_;
goto v___jp_3028_;
}
}
v___jp_3028_:
{
size_t v_sz_3030_; size_t v___x_3031_; lean_object* v___x_3032_; 
v_sz_3030_ = lean_array_size(v___y_3029_);
v___x_3031_ = ((size_t)0ULL);
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3030_, v___x_3031_, v___y_3029_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3033_; lean_object* v_env_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3033_ = lean_st_ref_get(v_a_2287_);
v_env_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_ref(v_env_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3036_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3037_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3035_, v_env_3034_, v___x_3036_);
v___x_3038_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3039_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3037_, v___x_3038_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3070_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3070_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3070_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_fst_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3068_; 
v_fst_3044_ = lean_ctor_get(v_a_3040_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_a_3040_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_a_3040_, 1);
lean_dec(v_unused_3069_);
v___x_3046_ = v_a_3040_;
v_isShared_3047_ = v_isSharedCheck_3068_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_fst_3044_);
lean_dec(v_a_3040_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3068_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
if (lean_obj_tag(v_fst_3044_) == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_del_object(v___x_3042_);
v___x_3048_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3049_ = l_Lean_MessageData_ofName(v___x_3036_);
lean_inc_ref(v___x_3049_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 7);
lean_ctor_set(v___x_3046_, 1, v___x_3049_);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3052_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3051_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3055_ = l_Lean_indentD(v___x_3054_);
v___x_3056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3053_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_3049_);
v___x_3060_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3061_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3062_;
}
}
else
{
lean_object* v_val_3064_; lean_object* v___x_3066_; 
lean_del_object(v___x_3046_);
lean_dec(v___x_3036_);
lean_dec(v_stx_2281_);
v_val_3064_ = lean_ctor_get(v_fst_3044_, 0);
lean_inc(v_val_3064_);
lean_dec_ref(v_fst_3044_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v_val_3064_);
v___x_3066_ = v___x_3042_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_val_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v___x_3036_);
lean_dec(v_stx_2281_);
v_a_3071_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3039_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3039_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v___x_3032_);
v___x_3079_ = lean_unsigned_to_nat(3u);
v___x_3080_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3079_);
lean_dec(v_stx_2281_);
v___x_3081_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3080_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3099_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3099_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3099_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
uint8_t v_returnsEarly_3086_; lean_object* v_reassigns_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3097_; 
v_returnsEarly_3086_ = lean_ctor_get_uint8(v_a_3082_, sizeof(void*)*2 + 2);
v_reassigns_3087_ = lean_ctor_get(v_a_3082_, 1);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_a_3082_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v_a_3082_, 0);
lean_dec(v_unused_3098_);
v___x_3089_ = v_a_3082_;
v_isShared_3090_ = v_isSharedCheck_3097_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_reassigns_3087_);
lean_dec(v_a_3082_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3097_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3027_);
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_reassigns_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3096_, sizeof(void*)*2 + 2, v_returnsEarly_3086_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*2, v___x_2456_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*2 + 1, v___x_2456_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3092_);
v___x_3094_ = v___x_3084_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
else
{
return v___x_3081_;
}
}
}
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_unsigned_to_nat(3u);
v___x_3119_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3118_);
lean_dec(v_stx_2281_);
v___x_3120_ = l_Lean_NameSet_empty;
v___x_3121_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3121_, 0, v___x_3117_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
lean_ctor_set_uint8(v___x_3121_, sizeof(void*)*2, v___x_2454_);
lean_ctor_set_uint8(v___x_3121_, sizeof(void*)*2 + 1, v___x_2454_);
lean_ctor_set_uint8(v___x_3121_, sizeof(void*)*2 + 2, v___x_2454_);
v___x_3122_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3119_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3131_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3121_, v_a_3123_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
else
{
lean_dec_ref(v___x_3121_);
return v___x_3122_;
}
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; size_t v_sz_3135_; size_t v___x_3136_; lean_object* v___x_3137_; 
v___x_3132_ = lean_unsigned_to_nat(4u);
v___x_3133_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3132_);
v___x_3134_ = l_Lean_Syntax_getArgs(v___x_3133_);
lean_dec(v___x_3133_);
v_sz_3135_ = lean_array_size(v___x_3134_);
v___x_3136_ = ((size_t)0ULL);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3135_, v___x_3136_, v___x_3134_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v___x_3138_; lean_object* v_env_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3138_ = lean_st_ref_get(v_a_2287_);
v_env_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_env_3139_);
lean_dec(v___x_3138_);
v___x_3140_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3141_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3142_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3140_, v_env_3139_, v___x_3141_);
v___x_3143_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3144_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3142_, v___x_3143_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3175_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3175_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3175_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v_fst_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3173_; 
v_fst_3149_ = lean_ctor_get(v_a_3145_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_a_3145_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v_a_3145_, 1);
lean_dec(v_unused_3174_);
v___x_3151_ = v_a_3145_;
v_isShared_3152_ = v_isSharedCheck_3173_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_fst_3149_);
lean_dec(v_a_3145_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3173_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
if (lean_obj_tag(v_fst_3149_) == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
lean_del_object(v___x_3147_);
v___x_3153_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3154_ = l_Lean_MessageData_ofName(v___x_3141_);
lean_inc_ref(v___x_3154_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set_tag(v___x_3151_, 7);
lean_ctor_set(v___x_3151_, 1, v___x_3154_);
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3156_ = v___x_3151_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3157_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3160_ = l_Lean_indentD(v___x_3159_);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3158_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3154_);
v___x_3165_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3166_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3167_;
}
}
else
{
lean_object* v_val_3169_; lean_object* v___x_3171_; 
lean_del_object(v___x_3151_);
lean_dec(v___x_3141_);
lean_dec(v_stx_2281_);
v_val_3169_ = lean_ctor_get(v_fst_3149_, 0);
lean_inc(v_val_3169_);
lean_dec_ref(v_fst_3149_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_val_3169_);
v___x_3171_ = v___x_3147_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_val_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v___x_3141_);
lean_dec(v_stx_2281_);
v_a_3176_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3144_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3144_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v_val_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3271_; 
v_val_3184_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3186_ = v___x_3137_;
v_isShared_3187_ = v_isSharedCheck_3271_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_val_3184_);
lean_dec(v___x_3137_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3271_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_elseSeq_x3f_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3188_ = lean_unsigned_to_nat(3u);
v___x_3189_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3188_);
v___x_3214_ = lean_unsigned_to_nat(5u);
v___x_3215_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3214_);
v___x_3216_ = l_Lean_Syntax_isNone(v___x_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3215_);
v___x_3218_ = l_Lean_Syntax_matchesNull(v___x_3215_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v_env_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec(v___x_3215_);
lean_dec(v___x_3189_);
lean_del_object(v___x_3186_);
lean_dec(v_val_3184_);
v___x_3219_ = lean_st_ref_get(v_a_2287_);
v_env_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc_ref(v_env_3220_);
lean_dec(v___x_3219_);
v___x_3221_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3222_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3223_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3221_, v_env_3220_, v___x_3222_);
v___x_3224_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3225_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3223_, v___x_3224_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3256_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3256_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3256_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_fst_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3254_; 
v_fst_3230_ = lean_ctor_get(v_a_3226_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3226_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; 
v_unused_3255_ = lean_ctor_get(v_a_3226_, 1);
lean_dec(v_unused_3255_);
v___x_3232_ = v_a_3226_;
v_isShared_3233_ = v_isSharedCheck_3254_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_fst_3230_);
lean_dec(v_a_3226_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3254_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
if (lean_obj_tag(v_fst_3230_) == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_del_object(v___x_3228_);
v___x_3234_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3235_ = l_Lean_MessageData_ofName(v___x_3222_);
lean_inc_ref(v___x_3235_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 7);
lean_ctor_set(v___x_3232_, 1, v___x_3235_);
lean_ctor_set(v___x_3232_, 0, v___x_3234_);
v___x_3237_ = v___x_3232_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3238_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3241_ = l_Lean_indentD(v___x_3240_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3239_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v___x_3235_);
v___x_3246_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3247_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3248_;
}
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3252_; 
lean_del_object(v___x_3232_);
lean_dec(v___x_3222_);
lean_dec(v_stx_2281_);
v_val_3250_ = lean_ctor_get(v_fst_3230_, 0);
lean_inc(v_val_3250_);
lean_dec_ref(v_fst_3230_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_val_3250_);
v___x_3252_ = v___x_3228_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_val_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v___x_3222_);
lean_dec(v_stx_2281_);
v_a_3257_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3225_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3225_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
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
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_dec(v_stx_2281_);
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = l_Lean_Syntax_getArg(v___x_3215_, v___x_3265_);
lean_dec(v___x_3215_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3266_);
v___x_3268_ = v___x_3186_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
v_elseSeq_x3f_3191_ = v___x_3268_;
v___y_3192_ = v_a_2282_;
v___y_3193_ = v_a_2283_;
v___y_3194_ = v_a_2284_;
v___y_3195_ = v_a_2285_;
v___y_3196_ = v_a_2286_;
v___y_3197_ = v_a_2287_;
goto v___jp_3190_;
}
}
}
else
{
lean_object* v___x_3270_; 
lean_dec(v___x_3215_);
lean_del_object(v___x_3186_);
lean_dec(v_stx_2281_);
v___x_3270_ = lean_box(0);
v_elseSeq_x3f_3191_ = v___x_3270_;
v___y_3192_ = v_a_2282_;
v___y_3193_ = v_a_2283_;
v___y_3194_ = v_a_2284_;
v___y_3195_ = v_a_2285_;
v___y_3196_ = v_a_2286_;
v___y_3197_ = v_a_2287_;
goto v___jp_3190_;
}
v___jp_3190_:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3200_; size_t v_sz_3201_; lean_object* v___x_3202_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref(v___x_3198_);
v___x_3200_ = l_Array_reverse___redArg(v_val_3184_);
v_sz_3201_ = lean_array_size(v___x_3200_);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3200_, v_sz_3201_, v___x_3136_, v_a_3199_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec_ref(v___x_3200_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref(v___x_3202_);
v___x_3204_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3189_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3213_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3207_ = v___x_3204_;
v_isShared_3208_ = v_isSharedCheck_3213_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3204_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3213_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3209_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3205_, v_a_3203_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3209_);
v___x_3211_ = v___x_3207_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
else
{
lean_dec(v_a_3203_);
return v___x_3204_;
}
}
else
{
lean_dec(v___x_3189_);
return v___x_3202_;
}
}
else
{
lean_dec(v___x_3189_);
lean_dec(v_val_3184_);
return v___x_3198_;
}
}
}
}
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3444_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3273_);
v___x_3445_ = l_Lean_Syntax_isNone(v___x_3444_);
if (v___x_3445_ == 0)
{
uint8_t v___x_3446_; 
lean_inc(v___x_3444_);
v___x_3446_ = l_Lean_Syntax_matchesNull(v___x_3444_, v___x_3273_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v_env_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v___x_3444_);
v___x_3447_ = lean_st_ref_get(v_a_2287_);
v_env_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc_ref(v_env_3448_);
lean_dec(v___x_3447_);
v___x_3449_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3450_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3451_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3449_, v_env_3448_, v___x_3450_);
v___x_3452_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3453_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3451_, v___x_3452_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3484_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3484_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3484_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_fst_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3482_; 
v_fst_3458_ = lean_ctor_get(v_a_3454_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_a_3454_);
if (v_isSharedCheck_3482_ == 0)
{
lean_object* v_unused_3483_; 
v_unused_3483_ = lean_ctor_get(v_a_3454_, 1);
lean_dec(v_unused_3483_);
v___x_3460_ = v_a_3454_;
v_isShared_3461_ = v_isSharedCheck_3482_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_fst_3458_);
lean_dec(v_a_3454_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3482_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
if (lean_obj_tag(v_fst_3458_) == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
lean_del_object(v___x_3456_);
v___x_3462_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3463_ = l_Lean_MessageData_ofName(v___x_3450_);
lean_inc_ref(v___x_3463_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set_tag(v___x_3460_, 7);
lean_ctor_set(v___x_3460_, 1, v___x_3463_);
lean_ctor_set(v___x_3460_, 0, v___x_3462_);
v___x_3465_ = v___x_3460_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3466_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3469_ = l_Lean_indentD(v___x_3468_);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3467_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v___x_3463_);
v___x_3474_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3475_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3476_;
}
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3480_; 
lean_del_object(v___x_3460_);
lean_dec(v___x_3450_);
lean_dec(v_stx_2281_);
v_val_3478_ = lean_ctor_get(v_fst_3458_, 0);
lean_inc(v_val_3478_);
lean_dec_ref(v_fst_3458_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v_val_3478_);
v___x_3480_ = v___x_3456_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_val_3478_);
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
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec(v___x_3450_);
lean_dec(v_stx_2281_);
v_a_3485_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3453_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3453_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = l_Lean_Syntax_getArg(v___x_3444_, v___x_3272_);
lean_dec(v___x_3444_);
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67));
v___x_3495_ = l_Lean_Syntax_isOfKind(v___x_3493_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v_env_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3496_ = lean_st_ref_get(v_a_2287_);
v_env_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc_ref(v_env_3497_);
lean_dec(v___x_3496_);
v___x_3498_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3499_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3500_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3498_, v_env_3497_, v___x_3499_);
v___x_3501_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3502_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3500_, v___x_3501_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3533_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3533_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3533_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_fst_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3531_; 
v_fst_3507_ = lean_ctor_get(v_a_3503_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3503_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v_a_3503_, 1);
lean_dec(v_unused_3532_);
v___x_3509_ = v_a_3503_;
v_isShared_3510_ = v_isSharedCheck_3531_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_fst_3507_);
lean_dec(v_a_3503_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3531_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
if (lean_obj_tag(v_fst_3507_) == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
lean_del_object(v___x_3505_);
v___x_3511_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3512_ = l_Lean_MessageData_ofName(v___x_3499_);
lean_inc_ref(v___x_3512_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set_tag(v___x_3509_, 7);
lean_ctor_set(v___x_3509_, 1, v___x_3512_);
lean_ctor_set(v___x_3509_, 0, v___x_3511_);
v___x_3514_ = v___x_3509_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3515_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3514_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3518_ = l_Lean_indentD(v___x_3517_);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3516_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v___x_3512_);
v___x_3523_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3524_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3525_;
}
}
else
{
lean_object* v_val_3527_; lean_object* v___x_3529_; 
lean_del_object(v___x_3509_);
lean_dec(v___x_3499_);
lean_dec(v_stx_2281_);
v_val_3527_ = lean_ctor_get(v_fst_3507_, 0);
lean_inc(v_val_3527_);
lean_dec_ref(v_fst_3507_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v_val_3527_);
v___x_3529_ = v___x_3505_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_val_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v___x_3499_);
lean_dec(v_stx_2281_);
v_a_3534_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3502_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3502_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
v___y_3339_ = v_a_2282_;
v___y_3340_ = v_a_2283_;
v___y_3341_ = v_a_2284_;
v___y_3342_ = v_a_2285_;
v___y_3343_ = v_a_2286_;
v___y_3344_ = v_a_2287_;
goto v___jp_3338_;
}
}
}
else
{
lean_dec(v___x_3444_);
v___y_3339_ = v_a_2282_;
v___y_3340_ = v_a_2283_;
v___y_3341_ = v_a_2284_;
v___y_3342_ = v_a_2285_;
v___y_3343_ = v_a_2286_;
v___y_3344_ = v_a_2287_;
goto v___jp_3338_;
}
v___jp_3274_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3281_ = lean_unsigned_to_nat(6u);
v___x_3282_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3281_);
v___x_3283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3282_);
v___x_3284_ = l_Lean_Syntax_isOfKind(v___x_3282_, v___x_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v_env_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec(v___x_3282_);
v___x_3285_ = lean_st_ref_get(v___y_3280_);
v_env_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc_ref(v_env_3286_);
lean_dec(v___x_3285_);
v___x_3287_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3288_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3289_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3287_, v_env_3286_, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3291_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3289_, v___x_3290_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3322_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3322_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3322_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v_fst_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3320_; 
v_fst_3296_ = lean_ctor_get(v_a_3292_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3292_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; 
v_unused_3321_ = lean_ctor_get(v_a_3292_, 1);
lean_dec(v_unused_3321_);
v___x_3298_ = v_a_3292_;
v_isShared_3299_ = v_isSharedCheck_3320_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_fst_3296_);
lean_dec(v_a_3292_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3320_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
if (lean_obj_tag(v_fst_3296_) == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
lean_del_object(v___x_3294_);
v___x_3300_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3301_ = l_Lean_MessageData_ofName(v___x_3288_);
lean_inc_ref(v___x_3301_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 7);
lean_ctor_set(v___x_3298_, 1, v___x_3301_);
lean_ctor_set(v___x_3298_, 0, v___x_3300_);
v___x_3303_ = v___x_3298_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3304_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3307_ = l_Lean_indentD(v___x_3306_);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3305_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3301_);
v___x_3312_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3313_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3314_;
}
}
else
{
lean_object* v_val_3316_; lean_object* v___x_3318_; 
lean_del_object(v___x_3298_);
lean_dec(v___x_3288_);
lean_dec(v_stx_2281_);
v_val_3316_ = lean_ctor_get(v_fst_3296_, 0);
lean_inc(v_val_3316_);
lean_dec_ref(v_fst_3296_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v_val_3316_);
v___x_3318_ = v___x_3294_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_val_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v___x_3288_);
lean_dec(v_stx_2281_);
v_a_3323_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3291_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3291_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; size_t v_sz_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
lean_dec(v_stx_2281_);
v___x_3331_ = l_Lean_Syntax_getArg(v___x_3282_, v___x_3272_);
lean_dec(v___x_3282_);
v___x_3332_ = l_Lean_Syntax_getArgs(v___x_3331_);
lean_dec(v___x_3331_);
v___x_3333_ = l_Lean_NameSet_empty;
v___x_3334_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3334_, 0, v___x_3273_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*2, v___x_2450_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*2 + 1, v___x_2450_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*2 + 2, v___x_2450_);
v_sz_3335_ = lean_array_size(v___x_3332_);
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2450_, v___x_3332_, v_sz_3335_, v___x_3336_, v___x_3334_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec_ref(v___x_3332_);
return v___x_3337_;
}
}
v___jp_3338_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3345_ = lean_unsigned_to_nat(2u);
v___x_3346_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3345_);
v___x_3347_ = l_Lean_Syntax_isNone(v___x_3346_);
if (v___x_3347_ == 0)
{
uint8_t v___x_3348_; 
lean_inc(v___x_3346_);
v___x_3348_ = l_Lean_Syntax_matchesNull(v___x_3346_, v___x_3273_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; lean_object* v_env_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec(v___x_3346_);
v___x_3349_ = lean_st_ref_get(v___y_3344_);
v_env_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_ref(v_env_3350_);
lean_dec(v___x_3349_);
v___x_3351_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3352_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3353_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3351_, v_env_3350_, v___x_3352_);
v___x_3354_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3355_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3353_, v___x_3354_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3386_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v_fst_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3384_; 
v_fst_3360_ = lean_ctor_get(v_a_3356_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_a_3356_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v_a_3356_, 1);
lean_dec(v_unused_3385_);
v___x_3362_ = v_a_3356_;
v_isShared_3363_ = v_isSharedCheck_3384_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_fst_3360_);
lean_dec(v_a_3356_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3384_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
if (lean_obj_tag(v_fst_3360_) == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
lean_del_object(v___x_3358_);
v___x_3364_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3365_ = l_Lean_MessageData_ofName(v___x_3352_);
lean_inc_ref(v___x_3365_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 7);
lean_ctor_set(v___x_3362_, 1, v___x_3365_);
lean_ctor_set(v___x_3362_, 0, v___x_3364_);
v___x_3367_ = v___x_3362_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3368_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3371_ = l_Lean_indentD(v___x_3370_);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3369_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v___x_3365_);
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3377_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
return v___x_3378_;
}
}
else
{
lean_object* v_val_3380_; lean_object* v___x_3382_; 
lean_del_object(v___x_3362_);
lean_dec(v___x_3352_);
lean_dec(v_stx_2281_);
v_val_3380_ = lean_ctor_get(v_fst_3360_, 0);
lean_inc(v_val_3380_);
lean_dec_ref(v_fst_3360_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v_val_3380_);
v___x_3382_ = v___x_3358_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_val_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v___x_3352_);
lean_dec(v_stx_2281_);
v_a_3387_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3355_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3355_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = l_Lean_Syntax_getArg(v___x_3346_, v___x_3272_);
lean_dec(v___x_3346_);
v___x_3396_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65));
v___x_3397_ = l_Lean_Syntax_isOfKind(v___x_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v_env_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3398_ = lean_st_ref_get(v___y_3344_);
v_env_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc_ref(v_env_3399_);
lean_dec(v___x_3398_);
v___x_3400_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3401_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3402_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3400_, v_env_3399_, v___x_3401_);
v___x_3403_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3404_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3402_, v___x_3403_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3435_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3435_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3435_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v_fst_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3433_; 
v_fst_3409_ = lean_ctor_get(v_a_3405_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v_a_3405_, 1);
lean_dec(v_unused_3434_);
v___x_3411_ = v_a_3405_;
v_isShared_3412_ = v_isSharedCheck_3433_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_fst_3409_);
lean_dec(v_a_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3433_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
if (lean_obj_tag(v_fst_3409_) == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_del_object(v___x_3407_);
v___x_3413_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3414_ = l_Lean_MessageData_ofName(v___x_3401_);
lean_inc_ref(v___x_3414_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 7);
lean_ctor_set(v___x_3411_, 1, v___x_3414_);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3416_ = v___x_3411_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3417_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3420_ = l_Lean_indentD(v___x_3419_);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3418_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
lean_ctor_set(v___x_3424_, 1, v___x_3414_);
v___x_3425_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3426_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
return v___x_3427_;
}
}
else
{
lean_object* v_val_3429_; lean_object* v___x_3431_; 
lean_del_object(v___x_3411_);
lean_dec(v___x_3401_);
lean_dec(v_stx_2281_);
v_val_3429_ = lean_ctor_get(v_fst_3409_, 0);
lean_inc(v_val_3429_);
lean_dec_ref(v_fst_3409_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v_val_3429_);
v___x_3431_ = v___x_3407_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_val_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___x_3401_);
lean_dec(v_stx_2281_);
v_a_3436_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3404_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3404_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
else
{
v___y_3275_ = v___y_3339_;
v___y_3276_ = v___y_3340_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3342_;
v___y_3279_ = v___y_3343_;
v___y_3280_ = v___y_3344_;
goto v___jp_3274_;
}
}
}
else
{
lean_dec(v___x_3346_);
v___y_3275_ = v___y_3339_;
v___y_3276_ = v___y_3340_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3342_;
v___y_3279_ = v___y_3343_;
v___y_3280_ = v___y_3344_;
goto v___jp_3274_;
}
}
}
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3542_ = lean_unsigned_to_nat(0u);
v___x_3543_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3542_);
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3543_);
v___x_3545_ = l_Lean_Syntax_isOfKind(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3546_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3543_);
v___x_3547_ = l_Lean_Syntax_isOfKind(v___x_3543_, v___x_3546_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v_env_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec(v___x_3543_);
v___x_3548_ = lean_st_ref_get(v_a_2287_);
v_env_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc_ref(v_env_3549_);
lean_dec(v___x_3548_);
v___x_3550_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3551_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3552_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3550_, v_env_3549_, v___x_3551_);
v___x_3553_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3554_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3552_, v___x_3553_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3585_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3585_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3585_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v_fst_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3583_; 
v_fst_3559_ = lean_ctor_get(v_a_3555_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_a_3555_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; 
v_unused_3584_ = lean_ctor_get(v_a_3555_, 1);
lean_dec(v_unused_3584_);
v___x_3561_ = v_a_3555_;
v_isShared_3562_ = v_isSharedCheck_3583_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_fst_3559_);
lean_dec(v_a_3555_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3583_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
if (lean_obj_tag(v_fst_3559_) == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
lean_del_object(v___x_3557_);
v___x_3563_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3564_ = l_Lean_MessageData_ofName(v___x_3551_);
lean_inc_ref(v___x_3564_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 7);
lean_ctor_set(v___x_3561_, 1, v___x_3564_);
lean_ctor_set(v___x_3561_, 0, v___x_3563_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3567_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3570_ = l_Lean_indentD(v___x_3569_);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3568_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
lean_ctor_set(v___x_3574_, 1, v___x_3564_);
v___x_3575_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3576_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3577_;
}
}
else
{
lean_object* v_val_3579_; lean_object* v___x_3581_; 
lean_del_object(v___x_3561_);
lean_dec(v___x_3551_);
lean_dec(v_stx_2281_);
v_val_3579_ = lean_ctor_get(v_fst_3559_, 0);
lean_inc(v_val_3579_);
lean_dec_ref(v_fst_3559_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v_val_3579_);
v___x_3581_ = v___x_3557_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_val_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v___x_3551_);
lean_dec(v_stx_2281_);
v_a_3586_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3554_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3554_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v___x_3594_; 
lean_dec(v_stx_2281_);
v___x_3594_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2418_, v___x_3543_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3594_;
}
}
else
{
lean_object* v___x_3595_; 
lean_dec(v_stx_2281_);
v___x_3595_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2418_, v___x_3543_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3595_;
}
}
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3596_ = lean_unsigned_to_nat(0u);
v___x_3597_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3596_);
v___x_3598_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69));
lean_inc(v___x_3597_);
v___x_3599_ = l_Lean_Syntax_isOfKind(v___x_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71));
lean_inc(v___x_3597_);
v___x_3601_ = l_Lean_Syntax_isOfKind(v___x_3597_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v_env_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec(v___x_3597_);
v___x_3602_ = lean_st_ref_get(v_a_2287_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v___x_3604_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3605_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3606_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3604_, v_env_3603_, v___x_3605_);
v___x_3607_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3608_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3606_, v___x_3607_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3639_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3611_ = v___x_3608_;
v_isShared_3612_ = v_isSharedCheck_3639_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3608_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3639_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v_fst_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3637_; 
v_fst_3613_ = lean_ctor_get(v_a_3609_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_a_3609_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v_a_3609_, 1);
lean_dec(v_unused_3638_);
v___x_3615_ = v_a_3609_;
v_isShared_3616_ = v_isSharedCheck_3637_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_fst_3613_);
lean_dec(v_a_3609_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3637_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
if (lean_obj_tag(v_fst_3613_) == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_del_object(v___x_3611_);
v___x_3617_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3618_ = l_Lean_MessageData_ofName(v___x_3605_);
lean_inc_ref(v___x_3618_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 7);
lean_ctor_set(v___x_3615_, 1, v___x_3618_);
lean_ctor_set(v___x_3615_, 0, v___x_3617_);
v___x_3620_ = v___x_3615_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3621_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3624_ = l_Lean_indentD(v___x_3623_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3622_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
lean_ctor_set(v___x_3628_, 1, v___x_3618_);
v___x_3629_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3630_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3631_;
}
}
else
{
lean_object* v_val_3633_; lean_object* v___x_3635_; 
lean_del_object(v___x_3615_);
lean_dec(v___x_3605_);
lean_dec(v_stx_2281_);
v_val_3633_ = lean_ctor_get(v_fst_3613_, 0);
lean_inc(v_val_3633_);
lean_dec_ref(v_fst_3613_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v_val_3633_);
v___x_3635_ = v___x_3611_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_val_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v___x_3605_);
lean_dec(v_stx_2281_);
v_a_3640_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3608_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3608_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_object* v___x_3648_; 
lean_dec(v_stx_2281_);
v___x_3648_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3597_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v___x_3597_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = lean_box(0);
v___x_3651_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3649_, v___x_3650_, v___x_3650_, v___x_3650_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3651_;
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_a_3652_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3648_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3648_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
else
{
lean_object* v___x_3660_; 
lean_dec(v_stx_2281_);
v___x_3660_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3597_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v___x_3597_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = lean_box(0);
v___x_3663_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3661_, v___x_3662_, v___x_3662_, v___x_3662_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3663_;
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
v_a_3664_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3660_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3660_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3672_ = lean_unsigned_to_nat(1u);
v___x_3673_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3672_);
v___x_3674_ = l_Lean_Syntax_isNone(v___x_3673_);
if (v___x_3674_ == 0)
{
uint8_t v___x_3675_; 
v___x_3675_ = l_Lean_Syntax_matchesNull(v___x_3673_, v___x_3672_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; lean_object* v_env_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3676_ = lean_st_ref_get(v_a_2287_);
v_env_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc_ref(v_env_3677_);
lean_dec(v___x_3676_);
v___x_3678_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3679_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3680_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3678_, v_env_3677_, v___x_3679_);
v___x_3681_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3682_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3680_, v___x_3681_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3713_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3713_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3713_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v_fst_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3711_; 
v_fst_3687_ = lean_ctor_get(v_a_3683_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_a_3683_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v_a_3683_, 1);
lean_dec(v_unused_3712_);
v___x_3689_ = v_a_3683_;
v_isShared_3690_ = v_isSharedCheck_3711_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_fst_3687_);
lean_dec(v_a_3683_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3711_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
if (lean_obj_tag(v_fst_3687_) == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
lean_del_object(v___x_3685_);
v___x_3691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3692_ = l_Lean_MessageData_ofName(v___x_3679_);
lean_inc_ref(v___x_3692_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 7);
lean_ctor_set(v___x_3689_, 1, v___x_3692_);
lean_ctor_set(v___x_3689_, 0, v___x_3691_);
v___x_3694_ = v___x_3689_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3695_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3698_ = l_Lean_indentD(v___x_3697_);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3696_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v___x_3692_);
v___x_3703_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3704_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3705_;
}
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3709_; 
lean_del_object(v___x_3689_);
lean_dec(v___x_3679_);
lean_dec(v_stx_2281_);
v_val_3707_ = lean_ctor_get(v_fst_3687_, 0);
lean_inc(v_val_3707_);
lean_dec_ref(v_fst_3687_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v_val_3707_);
v___x_3709_ = v___x_3685_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_val_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec(v___x_3679_);
lean_dec(v_stx_2281_);
v_a_3714_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3682_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3682_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
v___y_2436_ = v_a_2282_;
v___y_2437_ = v_a_2283_;
v___y_2438_ = v_a_2284_;
v___y_2439_ = v_a_2285_;
v___y_2440_ = v_a_2286_;
v___y_2441_ = v_a_2287_;
goto v___jp_2435_;
}
}
else
{
lean_dec(v___x_3673_);
v___y_2436_ = v_a_2282_;
v___y_2437_ = v_a_2283_;
v___y_2438_ = v_a_2284_;
v___y_2439_ = v_a_2285_;
v___y_2440_ = v_a_2286_;
v___y_2441_ = v_a_2287_;
goto v___jp_2435_;
}
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3722_ = lean_unsigned_to_nat(1u);
v___x_3723_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_isNone(v___x_3723_);
if (v___x_3724_ == 0)
{
uint8_t v___x_3725_; 
v___x_3725_ = l_Lean_Syntax_matchesNull(v___x_3723_, v___x_3722_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v_env_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3726_ = lean_st_ref_get(v_a_2287_);
v_env_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc_ref(v_env_3727_);
lean_dec(v___x_3726_);
v___x_3728_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3729_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3730_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3728_, v_env_3727_, v___x_3729_);
v___x_3731_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3732_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3730_, v___x_3731_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3763_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3763_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3763_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v_fst_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3761_; 
v_fst_3737_ = lean_ctor_get(v_a_3733_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_a_3733_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; 
v_unused_3762_ = lean_ctor_get(v_a_3733_, 1);
lean_dec(v_unused_3762_);
v___x_3739_ = v_a_3733_;
v_isShared_3740_ = v_isSharedCheck_3761_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_fst_3737_);
lean_dec(v_a_3733_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3761_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
if (lean_obj_tag(v_fst_3737_) == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_del_object(v___x_3735_);
v___x_3741_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3742_ = l_Lean_MessageData_ofName(v___x_3729_);
lean_inc_ref(v___x_3742_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set_tag(v___x_3739_, 7);
lean_ctor_set(v___x_3739_, 1, v___x_3742_);
lean_ctor_set(v___x_3739_, 0, v___x_3741_);
v___x_3744_ = v___x_3739_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3745_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3748_ = l_Lean_indentD(v___x_3747_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3746_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
lean_ctor_set(v___x_3752_, 1, v___x_3742_);
v___x_3753_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3754_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3755_;
}
}
else
{
lean_object* v_val_3757_; lean_object* v___x_3759_; 
lean_del_object(v___x_3739_);
lean_dec(v___x_3729_);
lean_dec(v_stx_2281_);
v_val_3757_ = lean_ctor_get(v_fst_3737_, 0);
lean_inc(v_val_3757_);
lean_dec_ref(v_fst_3737_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v_val_3757_);
v___x_3759_ = v___x_3735_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_val_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec(v___x_3729_);
lean_dec(v_stx_2281_);
v_a_3764_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3732_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3732_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
else
{
v___y_2303_ = v_a_2282_;
v___y_2304_ = v_a_2283_;
v___y_2305_ = v_a_2284_;
v___y_2306_ = v_a_2285_;
v___y_2307_ = v_a_2286_;
v___y_2308_ = v_a_2287_;
goto v___jp_2302_;
}
}
else
{
lean_dec(v___x_3723_);
v___y_2303_ = v_a_2282_;
v___y_2304_ = v_a_2283_;
v___y_2305_ = v_a_2284_;
v___y_2306_ = v_a_2285_;
v___y_2307_ = v_a_2286_;
v___y_2308_ = v_a_2287_;
goto v___jp_2302_;
}
}
v___jp_2435_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_unsigned_to_nat(2u);
v___x_2443_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2442_);
lean_dec(v_stx_2281_);
v___x_2444_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2434_, v___x_2443_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2444_;
}
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3772_ = lean_unsigned_to_nat(0u);
v___x_3773_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3772_);
v___x_3774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3775_ = l_Lean_Syntax_isOfKind(v___x_3773_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v_env_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3776_ = lean_st_ref_get(v_a_2287_);
v_env_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc_ref(v_env_3777_);
lean_dec(v___x_3776_);
v___x_3778_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3779_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3780_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3778_, v_env_3777_, v___x_3779_);
v___x_3781_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3782_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3780_, v___x_3781_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3813_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3813_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3813_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v_fst_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3811_; 
v_fst_3787_ = lean_ctor_get(v_a_3783_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v_a_3783_, 1);
lean_dec(v_unused_3812_);
v___x_3789_ = v_a_3783_;
v_isShared_3790_ = v_isSharedCheck_3811_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_fst_3787_);
lean_dec(v_a_3783_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3811_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
if (lean_obj_tag(v_fst_3787_) == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_del_object(v___x_3785_);
v___x_3791_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3792_ = l_Lean_MessageData_ofName(v___x_3779_);
lean_inc_ref(v___x_3792_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set_tag(v___x_3789_, 7);
lean_ctor_set(v___x_3789_, 1, v___x_3792_);
lean_ctor_set(v___x_3789_, 0, v___x_3791_);
v___x_3794_ = v___x_3789_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3795_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3794_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3798_ = l_Lean_indentD(v___x_3797_);
v___x_3799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3796_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3792_);
v___x_3803_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3804_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3805_;
}
}
else
{
lean_object* v_val_3807_; lean_object* v___x_3809_; 
lean_del_object(v___x_3789_);
lean_dec(v___x_3779_);
lean_dec(v_stx_2281_);
v_val_3807_ = lean_ctor_get(v_fst_3787_, 0);
lean_inc(v_val_3807_);
lean_dec_ref(v_fst_3787_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_val_3807_);
v___x_3809_ = v___x_3785_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_val_3807_);
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
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v___x_3779_);
lean_dec(v_stx_2281_);
v_a_3814_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3782_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3782_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v___x_3822_ = lean_unsigned_to_nat(1u);
v___x_3823_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3822_);
v___x_3824_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73));
lean_inc(v___x_3823_);
v___x_3825_ = l_Lean_Syntax_isOfKind(v___x_3823_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; lean_object* v_env_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec(v___x_3823_);
v___x_3826_ = lean_st_ref_get(v_a_2287_);
v_env_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc_ref(v_env_3827_);
lean_dec(v___x_3826_);
v___x_3828_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3829_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3830_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3828_, v_env_3827_, v___x_3829_);
v___x_3831_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3832_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3830_, v___x_3831_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3863_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3863_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3863_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v_fst_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3861_; 
v_fst_3837_ = lean_ctor_get(v_a_3833_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_a_3833_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; 
v_unused_3862_ = lean_ctor_get(v_a_3833_, 1);
lean_dec(v_unused_3862_);
v___x_3839_ = v_a_3833_;
v_isShared_3840_ = v_isSharedCheck_3861_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_fst_3837_);
lean_dec(v_a_3833_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3861_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
if (lean_obj_tag(v_fst_3837_) == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_del_object(v___x_3835_);
v___x_3841_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3842_ = l_Lean_MessageData_ofName(v___x_3829_);
lean_inc_ref(v___x_3842_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set_tag(v___x_3839_, 7);
lean_ctor_set(v___x_3839_, 1, v___x_3842_);
lean_ctor_set(v___x_3839_, 0, v___x_3841_);
v___x_3844_ = v___x_3839_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3845_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3848_ = l_Lean_indentD(v___x_3847_);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3846_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
lean_ctor_set(v___x_3852_, 1, v___x_3842_);
v___x_3853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3854_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3855_;
}
}
else
{
lean_object* v_val_3857_; lean_object* v___x_3859_; 
lean_del_object(v___x_3839_);
lean_dec(v___x_3829_);
lean_dec(v_stx_2281_);
v_val_3857_ = lean_ctor_get(v_fst_3837_, 0);
lean_inc(v_val_3857_);
lean_dec_ref(v_fst_3837_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v_val_3857_);
v___x_3859_ = v___x_3835_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_val_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v___x_3829_);
lean_dec(v_stx_2281_);
v_a_3864_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3832_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3832_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3872_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3772_);
lean_dec(v___x_3823_);
lean_inc(v___x_3872_);
v___x_3873_ = l_Lean_Syntax_matchesNull(v___x_3872_, v___x_3822_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v_env_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_dec(v___x_3872_);
v___x_3874_ = lean_st_ref_get(v_a_2287_);
v_env_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc_ref(v_env_3875_);
lean_dec(v___x_3874_);
v___x_3876_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3877_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3878_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3876_, v_env_3875_, v___x_3877_);
v___x_3879_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3880_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3878_, v___x_3879_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3911_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3883_ = v___x_3880_;
v_isShared_3884_ = v_isSharedCheck_3911_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3911_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v_fst_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3909_; 
v_fst_3885_ = lean_ctor_get(v_a_3881_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3881_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; 
v_unused_3910_ = lean_ctor_get(v_a_3881_, 1);
lean_dec(v_unused_3910_);
v___x_3887_ = v_a_3881_;
v_isShared_3888_ = v_isSharedCheck_3909_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_fst_3885_);
lean_dec(v_a_3881_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3909_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
if (lean_obj_tag(v_fst_3885_) == 0)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
lean_del_object(v___x_3883_);
v___x_3889_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3890_ = l_Lean_MessageData_ofName(v___x_3877_);
lean_inc_ref(v___x_3890_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set_tag(v___x_3887_, 7);
lean_ctor_set(v___x_3887_, 1, v___x_3890_);
lean_ctor_set(v___x_3887_, 0, v___x_3889_);
v___x_3892_ = v___x_3887_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3893_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3896_ = l_Lean_indentD(v___x_3895_);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3894_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v___x_3890_);
v___x_3901_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3902_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3903_;
}
}
else
{
lean_object* v_val_3905_; lean_object* v___x_3907_; 
lean_del_object(v___x_3887_);
lean_dec(v___x_3877_);
lean_dec(v_stx_2281_);
v_val_3905_ = lean_ctor_get(v_fst_3885_, 0);
lean_inc(v_val_3905_);
lean_dec_ref(v_fst_3885_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v_val_3905_);
v___x_3907_ = v___x_3883_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_val_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v___x_3877_);
lean_dec(v_stx_2281_);
v_a_3912_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3880_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3880_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3920_ = l_Lean_Syntax_getArg(v___x_3872_, v___x_3772_);
lean_dec(v___x_3872_);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75));
v___x_3922_ = l_Lean_Syntax_isOfKind(v___x_3920_, v___x_3921_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v_env_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3923_ = lean_st_ref_get(v_a_2287_);
v_env_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc_ref(v_env_3924_);
lean_dec(v___x_3923_);
v___x_3925_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3926_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3927_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3925_, v_env_3924_, v___x_3926_);
v___x_3928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3929_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3927_, v___x_3928_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3960_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3960_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3960_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v_fst_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3958_; 
v_fst_3934_ = lean_ctor_get(v_a_3930_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_a_3930_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v_a_3930_, 1);
lean_dec(v_unused_3959_);
v___x_3936_ = v_a_3930_;
v_isShared_3937_ = v_isSharedCheck_3958_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_fst_3934_);
lean_dec(v_a_3930_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3958_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
if (lean_obj_tag(v_fst_3934_) == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
lean_del_object(v___x_3932_);
v___x_3938_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3939_ = l_Lean_MessageData_ofName(v___x_3926_);
lean_inc_ref(v___x_3939_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set_tag(v___x_3936_, 7);
lean_ctor_set(v___x_3936_, 1, v___x_3939_);
lean_ctor_set(v___x_3936_, 0, v___x_3938_);
v___x_3941_ = v___x_3936_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3942_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3945_ = l_Lean_indentD(v___x_3944_);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3943_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
lean_ctor_set(v___x_3949_, 1, v___x_3939_);
v___x_3950_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3951_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_3952_;
}
}
else
{
lean_object* v_val_3954_; lean_object* v___x_3956_; 
lean_del_object(v___x_3936_);
lean_dec(v___x_3926_);
lean_dec(v_stx_2281_);
v_val_3954_ = lean_ctor_get(v_fst_3934_, 0);
lean_inc(v_val_3954_);
lean_dec_ref(v_fst_3934_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v_val_3954_);
v___x_3956_ = v___x_3932_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_val_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
lean_dec(v___x_3926_);
lean_dec(v_stx_2281_);
v_a_3961_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3929_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3929_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec(v_stx_2281_);
v___x_3969_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
}
}
}
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3971_ = lean_unsigned_to_nat(1u);
v___x_3972_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_3971_);
v___x_3973_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_3974_ = l_Lean_Syntax_isOfKind(v___x_3972_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v_env_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3975_ = lean_st_ref_get(v_a_2287_);
v_env_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc_ref(v_env_3976_);
lean_dec(v___x_3975_);
v___x_3977_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_3978_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_3979_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3977_, v_env_3976_, v___x_3978_);
v___x_3980_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3981_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_3979_, v___x_3980_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4012_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_4012_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4012_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v_fst_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4010_; 
v_fst_3986_ = lean_ctor_get(v_a_3982_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3982_);
if (v_isSharedCheck_4010_ == 0)
{
lean_object* v_unused_4011_; 
v_unused_4011_ = lean_ctor_get(v_a_3982_, 1);
lean_dec(v_unused_4011_);
v___x_3988_ = v_a_3982_;
v_isShared_3989_ = v_isSharedCheck_4010_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_fst_3986_);
lean_dec(v_a_3982_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4010_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
if (lean_obj_tag(v_fst_3986_) == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
lean_del_object(v___x_3984_);
v___x_3990_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3991_ = l_Lean_MessageData_ofName(v___x_3978_);
lean_inc_ref(v___x_3991_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set_tag(v___x_3988_, 7);
lean_ctor_set(v___x_3988_, 1, v___x_3991_);
lean_ctor_set(v___x_3988_, 0, v___x_3990_);
v___x_3993_ = v___x_3988_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3994_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_3997_ = l_Lean_indentD(v___x_3996_);
v___x_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3995_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3998_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
lean_ctor_set(v___x_4001_, 1, v___x_3991_);
v___x_4002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4003_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_4004_;
}
}
else
{
lean_object* v_val_4006_; lean_object* v___x_4008_; 
lean_del_object(v___x_3988_);
lean_dec(v___x_3978_);
lean_dec(v_stx_2281_);
v_val_4006_ = lean_ctor_get(v_fst_3986_, 0);
lean_inc(v_val_4006_);
lean_dec_ref(v_fst_3986_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v_val_4006_);
v___x_4008_ = v___x_3984_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_val_4006_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v___x_3978_);
lean_dec(v_stx_2281_);
v_a_4013_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3981_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3981_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
else
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_dec(v_stx_2281_);
v___x_4021_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
}
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4023_ = lean_unsigned_to_nat(1u);
v___x_4024_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_4023_);
v___x_4025_ = l_Lean_Syntax_isNone(v___x_4024_);
if (v___x_4025_ == 0)
{
uint8_t v___x_4026_; 
v___x_4026_ = l_Lean_Syntax_matchesNull(v___x_4024_, v___x_4023_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; lean_object* v_env_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_del_object(v___x_2339_);
v___x_4027_ = lean_st_ref_get(v_a_2287_);
v_env_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc_ref(v_env_4028_);
lean_dec(v___x_4027_);
v___x_4029_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_4030_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_4031_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4029_, v_env_4028_, v___x_4030_);
v___x_4032_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4033_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_4031_, v___x_4032_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4064_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4064_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4064_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v_fst_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4062_; 
v_fst_4038_ = lean_ctor_get(v_a_4034_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_a_4034_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; 
v_unused_4063_ = lean_ctor_get(v_a_4034_, 1);
lean_dec(v_unused_4063_);
v___x_4040_ = v_a_4034_;
v_isShared_4041_ = v_isSharedCheck_4062_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_fst_4038_);
lean_dec(v_a_4034_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4062_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
if (lean_obj_tag(v_fst_4038_) == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4045_; 
lean_del_object(v___x_4036_);
v___x_4042_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4043_ = l_Lean_MessageData_ofName(v___x_4030_);
lean_inc_ref(v___x_4043_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set_tag(v___x_4040_, 7);
lean_ctor_set(v___x_4040_, 1, v___x_4043_);
lean_ctor_set(v___x_4040_, 0, v___x_4042_);
v___x_4045_ = v___x_4040_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4046_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4045_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
v___x_4048_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_4049_ = l_Lean_indentD(v___x_4048_);
v___x_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4047_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___x_4051_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v___x_4043_);
v___x_4054_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4053_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4055_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_4056_;
}
}
else
{
lean_object* v_val_4058_; lean_object* v___x_4060_; 
lean_del_object(v___x_4040_);
lean_dec(v___x_4030_);
lean_dec(v_stx_2281_);
v_val_4058_ = lean_ctor_get(v_fst_4038_, 0);
lean_inc(v_val_4058_);
lean_dec_ref(v_fst_4038_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v_val_4058_);
v___x_4060_ = v___x_4036_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_val_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v___x_4030_);
lean_dec(v_stx_2281_);
v_a_4065_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4033_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4033_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
v___y_2356_ = v_a_2282_;
v___y_2357_ = v_a_2283_;
v___y_2358_ = v_a_2284_;
v___y_2359_ = v_a_2285_;
v___y_2360_ = v_a_2286_;
v___y_2361_ = v_a_2287_;
goto v___jp_2355_;
}
}
else
{
lean_dec(v___x_4024_);
v___y_2356_ = v_a_2282_;
v___y_2357_ = v_a_2283_;
v___y_2358_ = v_a_2284_;
v___y_2359_ = v_a_2285_;
v___y_2360_ = v_a_2286_;
v___y_2361_ = v_a_2287_;
goto v___jp_2355_;
}
}
}
else
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_del_object(v___x_2339_);
v___x_4073_ = lean_unsigned_to_nat(1u);
v___x_4074_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_4073_);
lean_dec(v_stx_2281_);
v___x_4075_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4074_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_4075_;
}
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_del_object(v___x_2339_);
lean_dec(v_stx_2281_);
v___x_4076_ = lean_unsigned_to_nat(1u);
v___x_4077_ = l_Lean_NameSet_empty;
v___x_4078_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*2, v___x_2422_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*2 + 1, v___x_2422_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*2 + 2, v___x_2422_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; 
lean_del_object(v___x_2339_);
v___x_4080_ = lean_unsigned_to_nat(0u);
v___x_4085_ = lean_unsigned_to_nat(1u);
v___x_4086_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_4085_);
v___x_4087_ = l_Lean_Syntax_isNone(v___x_4086_);
if (v___x_4087_ == 0)
{
uint8_t v___x_4088_; 
v___x_4088_ = l_Lean_Syntax_matchesNull(v___x_4086_, v___x_4085_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; lean_object* v_env_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4089_ = lean_st_ref_get(v_a_2287_);
v_env_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_ref(v_env_4090_);
lean_dec(v___x_4089_);
v___x_4091_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_4092_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_4093_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4091_, v_env_4090_, v___x_4092_);
v___x_4094_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4095_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_4093_, v___x_4094_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4126_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4126_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4126_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v_fst_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4124_; 
v_fst_4100_ = lean_ctor_get(v_a_4096_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_a_4096_);
if (v_isSharedCheck_4124_ == 0)
{
lean_object* v_unused_4125_; 
v_unused_4125_ = lean_ctor_get(v_a_4096_, 1);
lean_dec(v_unused_4125_);
v___x_4102_ = v_a_4096_;
v_isShared_4103_ = v_isSharedCheck_4124_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_fst_4100_);
lean_dec(v_a_4096_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4124_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
if (lean_obj_tag(v_fst_4100_) == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_del_object(v___x_4098_);
v___x_4104_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4105_ = l_Lean_MessageData_ofName(v___x_4092_);
lean_inc_ref(v___x_4105_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set_tag(v___x_4102_, 7);
lean_ctor_set(v___x_4102_, 1, v___x_4105_);
lean_ctor_set(v___x_4102_, 0, v___x_4104_);
v___x_4107_ = v___x_4102_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4108_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_4111_ = l_Lean_indentD(v___x_4110_);
v___x_4112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4109_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4112_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4105_);
v___x_4116_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4117_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_4118_;
}
}
else
{
lean_object* v_val_4120_; lean_object* v___x_4122_; 
lean_del_object(v___x_4102_);
lean_dec(v___x_4092_);
lean_dec(v_stx_2281_);
v_val_4120_ = lean_ctor_get(v_fst_4100_, 0);
lean_inc(v_val_4120_);
lean_dec_ref(v_fst_4100_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v_val_4120_);
v___x_4122_ = v___x_4098_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_val_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v___x_4092_);
lean_dec(v_stx_2281_);
v_a_4127_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4095_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4095_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
else
{
lean_dec(v_stx_2281_);
goto v___jp_4081_;
}
}
else
{
lean_dec(v___x_4086_);
lean_dec(v_stx_2281_);
goto v___jp_4081_;
}
v___jp_4081_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = l_Lean_NameSet_empty;
v___x_4083_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4083_, 0, v___x_4080_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
lean_ctor_set_uint8(v___x_4083_, sizeof(void*)*2, v___x_2420_);
lean_ctor_set_uint8(v___x_4083_, sizeof(void*)*2 + 1, v___x_2420_);
lean_ctor_set_uint8(v___x_4083_, sizeof(void*)*2 + 2, v___x_2418_);
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
}
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_del_object(v___x_2339_);
lean_dec(v_stx_2281_);
v___x_4135_ = lean_unsigned_to_nat(0u);
v___x_4136_ = l_Lean_NameSet_empty;
v___x_4137_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4137_, 0, v___x_4135_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
lean_ctor_set_uint8(v___x_4137_, sizeof(void*)*2, v___x_2417_);
lean_ctor_set_uint8(v___x_4137_, sizeof(void*)*2 + 1, v___x_2418_);
lean_ctor_set_uint8(v___x_4137_, sizeof(void*)*2 + 2, v___x_2417_);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
return v___x_4138_;
}
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_del_object(v___x_2339_);
lean_dec(v_stx_2281_);
v___x_4139_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
return v___x_4140_;
}
v___jp_2355_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2362_ = lean_unsigned_to_nat(2u);
v___x_2363_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2362_);
v___x_2364_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2365_ = l_Lean_Syntax_isOfKind(v___x_2363_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v_env_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_del_object(v___x_2339_);
v___x_2366_ = lean_st_ref_get(v___y_2361_);
v_env_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_ref(v_env_2367_);
lean_dec(v___x_2366_);
v___x_2368_ = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc_n(v_stx_2281_, 2);
v___x_2369_ = l_Lean_Syntax_getKind(v_stx_2281_);
v___x_2370_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2368_, v_env_2367_, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2372_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2281_, v___x_2370_, v___x_2371_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2403_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2403_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2403_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v_fst_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2401_; 
v_fst_2377_ = lean_ctor_get(v_a_2373_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v_a_2373_, 1);
lean_dec(v_unused_2402_);
v___x_2379_ = v_a_2373_;
v_isShared_2380_ = v_isSharedCheck_2401_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_fst_2377_);
lean_dec(v_a_2373_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2401_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
if (lean_obj_tag(v_fst_2377_) == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_del_object(v___x_2375_);
v___x_2381_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2382_ = l_Lean_MessageData_ofName(v___x_2369_);
lean_inc_ref(v___x_2382_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 7);
lean_ctor_set(v___x_2379_, 1, v___x_2382_);
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2385_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = l_Lean_MessageData_ofSyntax(v_stx_2281_);
v___x_2388_ = l_Lean_indentD(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v___x_2382_);
v___x_2393_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2394_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2395_;
}
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2399_; 
lean_del_object(v___x_2379_);
lean_dec(v___x_2369_);
lean_dec(v_stx_2281_);
v_val_2397_ = lean_ctor_get(v_fst_2377_, 0);
lean_inc(v_val_2397_);
lean_dec_ref(v_fst_2377_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v_val_2397_);
v___x_2399_ = v___x_2375_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_val_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v___x_2369_);
lean_dec(v_stx_2281_);
v_a_2404_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2372_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2372_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_dec(v_stx_2281_);
v___x_2412_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2412_);
v___x_2414_ = v___x_2339_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_stx_2281_);
v_a_4142_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_2336_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_2336_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
v___jp_2289_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2298_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2299_ = lean_box(0);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___y_2296_);
v___x_2301_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2298_, v___x_2299_, v___x_2300_, v___y_2297_, v___y_2291_, v___y_2290_, v___y_2294_, v___y_2293_, v___y_2292_, v___y_2295_);
return v___x_2301_;
}
v___jp_2302_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2309_ = lean_unsigned_to_nat(6u);
v___x_2310_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2309_);
v___x_2311_ = lean_unsigned_to_nat(7u);
v___x_2312_ = l_Lean_Syntax_getArg(v_stx_2281_, v___x_2311_);
lean_dec(v_stx_2281_);
v___x_2313_ = l_Lean_Syntax_getOptional_x3f(v___x_2312_);
lean_dec(v___x_2312_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_box(0);
v___y_2290_ = v___y_2304_;
v___y_2291_ = v___y_2303_;
v___y_2292_ = v___y_2307_;
v___y_2293_ = v___y_2306_;
v___y_2294_ = v___y_2305_;
v___y_2295_ = v___y_2308_;
v___y_2296_ = v___x_2310_;
v___y_2297_ = v___x_2314_;
goto v___jp_2289_;
}
else
{
lean_object* v_val_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_val_2315_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2313_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_val_2315_);
lean_dec(v___x_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_val_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
v___y_2290_ = v___y_2304_;
v___y_2291_ = v___y_2303_;
v___y_2292_ = v___y_2307_;
v___y_2293_ = v___y_2306_;
v___y_2294_ = v___y_2305_;
v___y_2295_ = v___y_2308_;
v___y_2296_ = v___x_2310_;
v___y_2297_ = v___x_2320_;
goto v___jp_2289_;
}
}
}
}
v___jp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2324_, v_bodyInfo_2325_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
v___jp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2329_, v_bodyInfo_2330_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4150_, size_t v_sz_4151_, size_t v_i_4152_, lean_object* v_b_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
uint8_t v___x_4161_; 
v___x_4161_ = lean_usize_dec_lt(v_i_4152_, v_sz_4151_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v_b_4153_);
return v___x_4162_;
}
else
{
uint8_t v_breaks_4163_; uint8_t v_continues_4164_; uint8_t v_returnsEarly_4165_; lean_object* v_numRegularExits_4166_; lean_object* v_reassigns_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v_breaks_4163_ = lean_ctor_get_uint8(v_b_4153_, sizeof(void*)*2);
v_continues_4164_ = lean_ctor_get_uint8(v_b_4153_, sizeof(void*)*2 + 1);
v_returnsEarly_4165_ = lean_ctor_get_uint8(v_b_4153_, sizeof(void*)*2 + 2);
v_numRegularExits_4166_ = lean_ctor_get(v_b_4153_, 0);
v_reassigns_4167_ = lean_ctor_get(v_b_4153_, 1);
v___x_4168_ = lean_unsigned_to_nat(0u);
v___x_4169_ = lean_nat_dec_eq(v_numRegularExits_4166_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4171_; 
lean_inc(v_reassigns_4167_);
lean_dec_ref(v_b_4153_);
v_a_4170_ = lean_array_uget_borrowed(v_as_4150_, v_i_4152_);
lean_inc(v_a_4170_);
v___x_4171_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4170_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; uint8_t v___y_4174_; uint8_t v___y_4175_; uint8_t v___y_4176_; uint8_t v___y_4191_; uint8_t v___y_4192_; uint8_t v___y_4195_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref(v___x_4171_);
if (v_breaks_4163_ == 0)
{
uint8_t v_breaks_4197_; 
v_breaks_4197_ = lean_ctor_get_uint8(v_a_4172_, sizeof(void*)*2);
v___y_4195_ = v_breaks_4197_;
goto v___jp_4194_;
}
else
{
v___y_4195_ = v___x_4161_;
goto v___jp_4194_;
}
v___jp_4173_:
{
lean_object* v_numRegularExits_4177_; lean_object* v_reassigns_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4189_; 
v_numRegularExits_4177_ = lean_ctor_get(v_a_4172_, 0);
v_reassigns_4178_ = lean_ctor_get(v_a_4172_, 1);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_a_4172_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4180_ = v_a_4172_;
v_isShared_4181_ = v_isSharedCheck_4189_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_reassigns_4178_);
lean_inc(v_numRegularExits_4177_);
lean_dec(v_a_4172_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4189_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4182_ = l_Lean_NameSet_append(v_reassigns_4167_, v_reassigns_4178_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 1, v___x_4182_);
v___x_4184_ = v___x_4180_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_numRegularExits_4177_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
size_t v___x_4185_; size_t v___x_4186_; 
lean_ctor_set_uint8(v___x_4184_, sizeof(void*)*2, v___y_4175_);
lean_ctor_set_uint8(v___x_4184_, sizeof(void*)*2 + 1, v___y_4174_);
lean_ctor_set_uint8(v___x_4184_, sizeof(void*)*2 + 2, v___y_4176_);
v___x_4185_ = ((size_t)1ULL);
v___x_4186_ = lean_usize_add(v_i_4152_, v___x_4185_);
v_i_4152_ = v___x_4186_;
v_b_4153_ = v___x_4184_;
goto _start;
}
}
}
v___jp_4190_:
{
if (v_returnsEarly_4165_ == 0)
{
uint8_t v_returnsEarly_4193_; 
v_returnsEarly_4193_ = lean_ctor_get_uint8(v_a_4172_, sizeof(void*)*2 + 2);
v___y_4174_ = v___y_4192_;
v___y_4175_ = v___y_4191_;
v___y_4176_ = v_returnsEarly_4193_;
goto v___jp_4173_;
}
else
{
v___y_4174_ = v___y_4192_;
v___y_4175_ = v___y_4191_;
v___y_4176_ = v___x_4161_;
goto v___jp_4173_;
}
}
v___jp_4194_:
{
if (v_continues_4164_ == 0)
{
uint8_t v_continues_4196_; 
v_continues_4196_ = lean_ctor_get_uint8(v_a_4172_, sizeof(void*)*2 + 1);
v___y_4191_ = v___y_4195_;
v___y_4192_ = v_continues_4196_;
goto v___jp_4190_;
}
else
{
v___y_4191_ = v___y_4195_;
v___y_4192_ = v___x_4161_;
goto v___jp_4190_;
}
}
}
else
{
lean_dec(v_reassigns_4167_);
return v___x_4171_;
}
}
else
{
lean_object* v___x_4198_; 
v___x_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4198_, 0, v_b_4153_);
return v___x_4198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v_info_4207_; lean_object* v___x_4208_; size_t v_sz_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
v_info_4207_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___x_4208_ = l_Lean_Parser_Term_getDoElems(v_stx_4199_);
v_sz_4209_ = lean_array_size(v___x_4208_);
v___x_4210_ = ((size_t)0ULL);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4208_, v_sz_4209_, v___x_4210_, v_info_4207_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec_ref(v___x_4208_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4221_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
lean_dec(v_a_4225_);
lean_dec_ref(v_a_4224_);
lean_dec(v_a_4223_);
lean_dec_ref(v_a_4222_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4230_, lean_object* v_sz_4231_, lean_object* v_i_4232_, lean_object* v_b_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
size_t v_sz_boxed_4241_; size_t v_i_boxed_4242_; lean_object* v_res_4243_; 
v_sz_boxed_4241_ = lean_unbox_usize(v_sz_4231_);
lean_dec(v_sz_4231_);
v_i_boxed_4242_ = lean_unbox_usize(v_i_4232_);
lean_dec(v_i_4232_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4230_, v_sz_boxed_4241_, v_i_boxed_4242_, v_b_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec_ref(v_as_4230_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4244_, lean_object* v_sz_4245_, lean_object* v_i_4246_, lean_object* v_b_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
size_t v_sz_boxed_4255_; size_t v_i_boxed_4256_; lean_object* v_res_4257_; 
v_sz_boxed_4255_ = lean_unbox_usize(v_sz_4245_);
lean_dec(v_sz_4245_);
v_i_boxed_4256_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_res_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4244_, v_sz_boxed_4255_, v_i_boxed_4256_, v_b_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec_ref(v_as_4244_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4258_, lean_object* v_rhs_x3f_4259_, lean_object* v_otherwise_x3f_4260_, lean_object* v_body_x3f_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4258_, v_rhs_x3f_4259_, v_otherwise_x3f_4260_, v_body_x3f_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4270_, lean_object* v_as_4271_, lean_object* v_sz_4272_, lean_object* v_i_4273_, lean_object* v_b_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
uint8_t v___x_261831__boxed_4282_; size_t v_sz_boxed_4283_; size_t v_i_boxed_4284_; lean_object* v_res_4285_; 
v___x_261831__boxed_4282_ = lean_unbox(v___x_4270_);
v_sz_boxed_4283_ = lean_unbox_usize(v_sz_4272_);
lean_dec(v_sz_4272_);
v_i_boxed_4284_ = lean_unbox_usize(v_i_4273_);
lean_dec(v_i_4273_);
v_res_4285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_261831__boxed_4282_, v_as_4271_, v_sz_boxed_4283_, v_i_boxed_4284_, v_b_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec_ref(v_as_4271_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4286_, lean_object* v_as_4287_, lean_object* v_sz_4288_, lean_object* v_i_4289_, lean_object* v_b_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
uint8_t v___x_261882__boxed_4298_; size_t v_sz_boxed_4299_; size_t v_i_boxed_4300_; lean_object* v_res_4301_; 
v___x_261882__boxed_4298_ = lean_unbox(v___x_4286_);
v_sz_boxed_4299_ = lean_unbox_usize(v_sz_4288_);
lean_dec(v_sz_4288_);
v_i_boxed_4300_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_261882__boxed_4298_, v_as_4287_, v_sz_boxed_4299_, v_i_boxed_4300_, v_b_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_as_4287_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4302_, lean_object* v_sz_4303_, lean_object* v_i_4304_, lean_object* v_b_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
size_t v_sz_boxed_4313_; size_t v_i_boxed_4314_; lean_object* v_res_4315_; 
v_sz_boxed_4313_ = lean_unbox_usize(v_sz_4303_);
lean_dec(v_sz_4303_);
v_i_boxed_4314_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_res_4315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4302_, v_sz_boxed_4313_, v_i_boxed_4314_, v_b_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v_as_4302_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4316_, lean_object* v_decl_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
uint8_t v_reassignment_boxed_4325_; lean_object* v_res_4326_; 
v_reassignment_boxed_4325_ = lean_unbox(v_reassignment_4316_);
v_res_4326_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4325_, v_decl_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4354_, lean_object* v_ref_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4355_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4364_, lean_object* v_ref_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4364_, v_ref_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4374_, lean_object* v_x_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4384_, lean_object* v_x_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4384_, v_x_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4394_, lean_object* v_as_4395_, lean_object* v_as_x27_4396_, lean_object* v_b_4397_, lean_object* v_a_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4394_, v_as_x27_4396_, v_b_4397_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4407_, lean_object* v_as_4408_, lean_object* v_as_x27_4409_, lean_object* v_b_4410_, lean_object* v_a_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4407_, v_as_4408_, v_as_x27_4409_, v_b_4410_, v_a_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v_as_4408_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4420_, lean_object* v_msg_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4430_, lean_object* v_msg_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4430_, v_msg_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4440_, lean_object* v_msg_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4440_, v_msg_4441_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4450_, lean_object* v_msg_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4450_, v_msg_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4460_, lean_object* v_as_x27_4461_, lean_object* v_b_4462_, lean_object* v_a_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4461_, v_b_4462_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4472_, lean_object* v_as_x27_4473_, lean_object* v_b_4474_, lean_object* v_a_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4472_, v_as_x27_4473_, v_b_4474_, v_a_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v_as_4472_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4484_, lean_object* v_ref_4485_, lean_object* v_msg_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4485_, v_msg_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4495_, lean_object* v_ref_4496_, lean_object* v_msg_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4495_, v_ref_4496_, v_msg_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v_ref_4496_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4506_, lean_object* v_macroStack_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4506_, v_macroStack_4507_, v___y_4512_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4516_, lean_object* v_macroStack_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4516_, v_macroStack_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4526_, lean_object* v_m_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v___x_4529_; 
v___x_4529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4527_, v_a_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4530_, lean_object* v_m_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4530_, v_m_4531_, v_a_4532_);
lean_dec(v_a_4532_);
lean_dec_ref(v_m_4531_);
return v_res_4533_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4534_, lean_object* v_x_4535_, lean_object* v_x_4536_){
_start:
{
uint8_t v___x_4537_; 
v___x_4537_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4535_, v_x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4538_, lean_object* v_x_4539_, lean_object* v_x_4540_){
_start:
{
uint8_t v_res_4541_; lean_object* v_r_4542_; 
v_res_4541_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4538_, v_x_4539_, v_x_4540_);
lean_dec_ref(v_x_4540_);
lean_dec_ref(v_x_4539_);
v_r_4542_ = lean_box(v_res_4541_);
return v_r_4542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4543_, lean_object* v_a_4544_, lean_object* v_x_4545_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4544_, v_x_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4547_, lean_object* v_a_4548_, lean_object* v_x_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4547_, v_a_4548_, v_x_4549_);
lean_dec(v_x_4549_);
lean_dec(v_a_4548_);
return v_res_4550_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4551_, lean_object* v_x_4552_, size_t v_x_4553_, lean_object* v_x_4554_){
_start:
{
uint8_t v___x_4555_; 
v___x_4555_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4552_, v_x_4553_, v_x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4556_, lean_object* v_x_4557_, lean_object* v_x_4558_, lean_object* v_x_4559_){
_start:
{
size_t v_x_267143__boxed_4560_; uint8_t v_res_4561_; lean_object* v_r_4562_; 
v_x_267143__boxed_4560_ = lean_unbox_usize(v_x_4558_);
lean_dec(v_x_4558_);
v_res_4561_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4556_, v_x_4557_, v_x_267143__boxed_4560_, v_x_4559_);
lean_dec_ref(v_x_4559_);
lean_dec_ref(v_x_4557_);
v_r_4562_ = lean_box(v_res_4561_);
return v_r_4562_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4563_, lean_object* v_keys_4564_, lean_object* v_vals_4565_, lean_object* v_heq_4566_, lean_object* v_i_4567_, lean_object* v_k_4568_){
_start:
{
uint8_t v___x_4569_; 
v___x_4569_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4564_, v_i_4567_, v_k_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4570_, lean_object* v_keys_4571_, lean_object* v_vals_4572_, lean_object* v_heq_4573_, lean_object* v_i_4574_, lean_object* v_k_4575_){
_start:
{
uint8_t v_res_4576_; lean_object* v_r_4577_; 
v_res_4576_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4570_, v_keys_4571_, v_vals_4572_, v_heq_4573_, v_i_4574_, v_k_4575_);
lean_dec_ref(v_k_4575_);
lean_dec_ref(v_vals_4572_);
lean_dec_ref(v_keys_4571_);
v_r_4577_ = lean_box(v_res_4576_);
return v_r_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4613_;
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
