// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndInfo
// Imports: public import Lean.Meta.Basic public import Lean.ReservedNameAction
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqFunIndParamKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqFunIndParamKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqFunIndParamKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqFunIndParamKind___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqFunIndParamKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqFunIndParamKind = (const lean_object*)&l_Lean_Meta_instBEqFunIndParamKind___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.FunIndParamKind.dropped"};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.FunIndParamKind.param"};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.FunIndParamKind.target"};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprFunIndParamKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprFunIndParamKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprFunIndParamKind___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprFunIndParamKind = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind;
static const lean_array_object l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFunIndInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFunIndInfo;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprFunIndInfo_repr_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "funName"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "funIndName"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "levelMask"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprFunIndInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprFunIndInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprFunIndInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprFunIndInfo = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funIndInfoExt"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 166, 99, 175, 176, 185, 8, 131)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_funIndInfoExt;
static const lean_string_object l_Lean_Meta_getFunInductName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l_Lean_Meta_getFunInductName___closed__0 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getFunInductName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunInductName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 227, 157, 243, 169, 45, 185, 145)}};
static const lean_object* l_Lean_Meta_getFunInductName___closed__1 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__1_value;
static const lean_string_object l_Lean_Meta_getFunInductName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "induct_unfolding"};
static const lean_object* l_Lean_Meta_getFunInductName___closed__2 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__2_value;
static const lean_ctor_object l_Lean_Meta_getFunInductName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunInductName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 44, 9, 205, 255, 228, 185, 244)}};
static const lean_object* l_Lean_Meta_getFunInductName___closed__3 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getFunCasesName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fun_cases"};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__0 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getFunCasesName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunCasesName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 179, 52, 186, 51, 24, 50, 193)}};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__1 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__1_value;
static const lean_string_object l_Lean_Meta_getFunCasesName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fun_cases_unfolding"};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__2 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__2_value;
static const lean_ctor_object l_Lean_Meta_getFunCasesName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunCasesName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 243, 0, 15, 80, 212, 101, 186)}};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__3 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getMutualInductName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mutual_induct"};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__0 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getMutualInductName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getMutualInductName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 83, 25, 196, 5, 111, 46, 167)}};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__1 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__1_value;
static const lean_string_object l_Lean_Meta_getMutualInductName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "mutual_induct_unfolding"};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__2 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__2_value;
static const lean_ctor_object l_Lean_Meta_getMutualInductName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getMutualInductName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 58, 37, 55, 35, 7, 46, 118)}};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__3 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__0;
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__1;
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__2;
static const lean_string_object l_Lean_Meta_setFunIndInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Tactic.FunIndInfo"};
static const lean_object* l_Lean_Meta_setFunIndInfo___closed__3 = (const lean_object*)&l_Lean_Meta_setFunIndInfo___closed__3_value;
static const lean_string_object l_Lean_Meta_setFunIndInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.setFunIndInfo"};
static const lean_object* l_Lean_Meta_setFunIndInfo___closed__4 = (const lean_object*)&l_Lean_Meta_setFunIndInfo___closed__4_value;
static const lean_string_object l_Lean_Meta_setFunIndInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 144, .m_capacity = 144, .m_length = 143, .m_data = "assertion violation: !(funIndInfoExt.contains ( __do_lift._@.Lean.Meta.Tactic.FunIndInfo.992483078._hygCtx._hyg.9.0 ) funIndInfo.funIndName)\n  "};
static const lean_object* l_Lean_Meta_setFunIndInfo___closed__5 = (const lean_object*)&l_Lean_Meta_setFunIndInfo___closed__5_value;
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Meta_FunIndParamKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_FunIndParamKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Meta_FunIndParamKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(lean_object* v_dropped_28_){
_start:
{
lean_inc(v_dropped_28_);
return v_dropped_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg___boxed(lean_object* v_dropped_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(v_dropped_29_);
lean_dec(v_dropped_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_dropped_34_){
_start:
{
lean_inc(v_dropped_34_);
return v_dropped_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_dropped_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Meta_FunIndParamKind_dropped_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_dropped_38_);
lean_dec(v_dropped_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg(lean_object* v_param_41_){
_start:
{
lean_inc(v_param_41_);
return v_param_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg___boxed(lean_object* v_param_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_FunIndParamKind_param_elim___redArg(v_param_42_);
lean_dec(v_param_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_param_47_){
_start:
{
lean_inc(v_param_47_);
return v_param_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_param_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Meta_FunIndParamKind_param_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_param_51_);
lean_dec(v_param_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg(lean_object* v_target_54_){
_start:
{
lean_inc(v_target_54_);
return v_target_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg___boxed(lean_object* v_target_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_FunIndParamKind_target_elim___redArg(v_target_55_);
lean_dec(v_target_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_target_60_){
_start:
{
lean_inc(v_target_60_);
return v_target_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_target_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Meta_FunIndParamKind_target_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_target_64_);
lean_dec(v_target_64_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqFunIndParamKind_beq(uint8_t v_x_67_, uint8_t v_y_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_x_67_);
v___x_70_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_y_68_);
v___x_71_ = lean_nat_dec_eq(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind_beq___boxed(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v_x_17__boxed_74_; uint8_t v_y_18__boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_x_17__boxed_74_ = lean_unbox(v_x_72_);
v_y_18__boxed_75_ = lean_unbox(v_y_73_);
v_res_76_ = l_Lean_Meta_instBEqFunIndParamKind_beq(v_x_17__boxed_74_, v_y_18__boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(2u);
v___x_90_ = lean_nat_to_int(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr(uint8_t v_x_93_, lean_object* v_prec_94_){
_start:
{
lean_object* v___y_96_; lean_object* v___y_103_; lean_object* v___y_110_; 
switch(v_x_93_)
{
case 0:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1024u);
v___x_117_ = lean_nat_dec_le(v___x_116_, v_prec_94_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__6, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6);
v___y_96_ = v___x_118_;
goto v___jp_95_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__7, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7);
v___y_96_ = v___x_119_;
goto v___jp_95_;
}
}
case 1:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1024u);
v___x_121_ = lean_nat_dec_le(v___x_120_, v_prec_94_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__6, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6);
v___y_103_ = v___x_122_;
goto v___jp_102_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__7, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7);
v___y_103_ = v___x_123_;
goto v___jp_102_;
}
}
default: 
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1024u);
v___x_125_ = lean_nat_dec_le(v___x_124_, v_prec_94_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__6, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6);
v___y_110_ = v___x_126_;
goto v___jp_109_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__7, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7);
v___y_110_ = v___x_127_;
goto v___jp_109_;
}
}
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = ((lean_object*)(l_Lean_Meta_instReprFunIndParamKind_repr___closed__1));
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
v___x_101_ = l_Repr_addAppParen(v___x_100_, v_prec_94_);
return v___x_101_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = ((lean_object*)(l_Lean_Meta_instReprFunIndParamKind_repr___closed__3));
v___x_105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_105_, 0, v___y_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_106_);
v___x_108_ = l_Repr_addAppParen(v___x_107_, v_prec_94_);
return v___x_108_;
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = ((lean_object*)(l_Lean_Meta_instReprFunIndParamKind_repr___closed__5));
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___y_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_prec_94_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___boxed(lean_object* v_x_128_, lean_object* v_prec_129_){
_start:
{
uint8_t v_x_177__boxed_130_; lean_object* v_res_131_; 
v_x_177__boxed_130_ = lean_unbox(v_x_128_);
v_res_131_ = l_Lean_Meta_instReprFunIndParamKind_repr(v_x_177__boxed_130_, v_prec_129_);
lean_dec(v_prec_129_);
return v_res_131_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedFunIndParamKind_default(void){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedFunIndParamKind(void){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0));
v___x_139_ = lean_box(0);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
lean_ctor_set(v___x_140_, 2, v___x_138_);
lean_ctor_set(v___x_140_, 3, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo_default(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1, &l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_instInhabitedFunIndInfo_default;
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprFunIndInfo_repr_spec__2(lean_object* v_a_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_nat_to_int(v_a_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_dec(v_x_145_);
return v_x_146_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_head_148_ = lean_ctor_get(v_x_147_, 0);
v_tail_149_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_160_ == 0)
{
v___x_151_ = v_x_147_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_tail_149_);
lean_inc(v_head_148_);
lean_dec(v_x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
lean_inc(v_x_145_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 5);
lean_ctor_set(v___x_151_, 1, v_x_145_);
lean_ctor_set(v___x_151_, 0, v_x_146_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_x_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_x_145_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unbox(v_head_148_);
lean_dec(v_head_148_);
v___x_156_ = l_Bool_repr___redArg(v___x_155_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v_x_146_ = v___x_157_;
v_x_147_ = v_tail_149_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_dec(v_x_161_);
return v_x_162_;
}
else
{
lean_object* v_head_164_; lean_object* v_tail_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_176_; 
v_head_164_ = lean_ctor_get(v_x_163_, 0);
v_tail_165_ = lean_ctor_get(v_x_163_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_176_ == 0)
{
v___x_167_ = v_x_163_;
v_isShared_168_ = v_isSharedCheck_176_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_tail_165_);
lean_inc(v_head_164_);
lean_dec(v_x_163_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_176_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
lean_inc(v_x_161_);
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 5);
lean_ctor_set(v___x_167_, 1, v_x_161_);
lean_ctor_set(v___x_167_, 0, v_x_162_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_x_162_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_x_161_);
v___x_170_ = v_reuseFailAlloc_175_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = lean_unbox(v_head_164_);
lean_dec(v_head_164_);
v___x_172_ = l_Bool_repr___redArg(v___x_171_);
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_161_, v___x_173_, v_tail_165_);
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_179_; 
lean_dec(v_x_178_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v_tail_180_; 
v_tail_180_ = lean_ctor_get(v_x_177_, 1);
if (lean_obj_tag(v_tail_180_) == 0)
{
lean_object* v_head_181_; uint8_t v___x_182_; lean_object* v___x_183_; 
lean_dec(v_x_178_);
v_head_181_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_head_181_);
lean_dec_ref(v_x_177_);
v___x_182_ = lean_unbox(v_head_181_);
lean_dec(v_head_181_);
v___x_183_ = l_Bool_repr___redArg(v___x_182_);
return v___x_183_;
}
else
{
lean_object* v_head_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_inc(v_tail_180_);
v_head_184_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_head_184_);
lean_dec_ref(v_x_177_);
v___x_185_ = lean_unbox(v_head_184_);
lean_dec(v_head_184_);
v___x_186_ = l_Bool_repr___redArg(v___x_185_);
v___x_187_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(v_x_178_, v___x_186_, v_tail_180_);
return v___x_187_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0));
v___x_197_ = lean_string_length(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5);
v___x_199_ = lean_nat_to_int(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(lean_object* v_xs_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = lean_array_get_size(v_xs_207_);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_nat_dec_eq(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_211_ = lean_array_to_list(v_xs_207_);
v___x_212_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3));
v___x_213_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(v___x_211_, v___x_212_);
v___x_214_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6);
v___x_215_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7));
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_213_);
v___x_217_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8));
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_214_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = l_Std_Format_fill(v___x_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
lean_dec_ref(v_xs_207_);
v___x_221_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10));
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_dec(v_x_222_);
return v_x_223_;
}
else
{
lean_object* v_head_225_; lean_object* v_tail_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_238_; 
v_head_225_ = lean_ctor_get(v_x_224_, 0);
v_tail_226_ = lean_ctor_get(v_x_224_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_238_ == 0)
{
v___x_228_ = v_x_224_;
v_isShared_229_ = v_isSharedCheck_238_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_tail_226_);
lean_inc(v_head_225_);
lean_dec(v_x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_238_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
lean_inc(v_x_222_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 5);
lean_ctor_set(v___x_228_, 1, v_x_222_);
lean_ctor_set(v___x_228_, 0, v_x_223_);
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_x_223_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_x_222_);
v___x_231_ = v_reuseFailAlloc_237_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_unbox(v_head_225_);
lean_dec(v_head_225_);
v___x_234_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___x_233_, v___x_232_);
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_231_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v_x_223_ = v___x_235_;
v_x_224_ = v_tail_226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_dec(v_x_239_);
return v_x_240_;
}
else
{
lean_object* v_head_242_; lean_object* v_tail_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_255_; 
v_head_242_ = lean_ctor_get(v_x_241_, 0);
v_tail_243_ = lean_ctor_get(v_x_241_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_255_ == 0)
{
v___x_245_ = v_x_241_;
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_tail_243_);
lean_inc(v_head_242_);
lean_dec(v_x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
lean_inc(v_x_239_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 5);
lean_ctor_set(v___x_245_, 1, v_x_239_);
lean_ctor_set(v___x_245_, 0, v_x_240_);
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_x_240_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_x_239_);
v___x_248_ = v_reuseFailAlloc_254_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_unbox(v_head_242_);
lean_dec(v_head_242_);
v___x_251_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___x_250_, v___x_249_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_248_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(v_x_239_, v___x_252_, v_tail_243_);
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(uint8_t v___y_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___y_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0___boxed(lean_object* v___y_259_){
_start:
{
uint8_t v___y_842__boxed_260_; lean_object* v_res_261_; 
v___y_842__boxed_260_ = lean_unbox(v___y_259_);
v_res_261_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___y_842__boxed_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v___x_264_; 
lean_dec(v_x_263_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v_tail_265_; 
v_tail_265_ = lean_ctor_get(v_x_262_, 1);
if (lean_obj_tag(v_tail_265_) == 0)
{
lean_object* v_head_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
lean_dec(v_x_263_);
v_head_266_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_head_266_);
lean_dec_ref(v_x_262_);
v___x_267_ = lean_unbox(v_head_266_);
lean_dec(v_head_266_);
v___x_268_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___x_267_);
return v___x_268_;
}
else
{
lean_object* v_head_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_inc(v_tail_265_);
v_head_269_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_head_269_);
lean_dec_ref(v_x_262_);
v___x_270_ = lean_unbox(v_head_269_);
lean_dec(v_head_269_);
v___x_271_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___x_270_);
v___x_272_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(v_x_263_, v___x_271_, v_tail_265_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(lean_object* v_xs_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_array_get_size(v_xs_273_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_nat_dec_eq(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_277_ = lean_array_to_list(v_xs_273_);
v___x_278_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3));
v___x_279_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(v___x_277_, v___x_278_);
v___x_280_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6);
v___x_281_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7));
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_279_);
v___x_283_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_280_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = l_Std_Format_fill(v___x_285_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; 
lean_dec_ref(v_xs_273_);
v___x_287_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10));
return v___x_287_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(11u);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(14u);
v___x_307_ = lean_nat_to_int(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(13u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(10u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0));
v___x_320_ = lean_string_length(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg(lean_object* v_x_327_){
_start:
{
lean_object* v_funName_328_; lean_object* v_funIndName_329_; lean_object* v_levelMask_330_; lean_object* v_params_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_funName_328_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_funName_328_);
v_funIndName_329_ = lean_ctor_get(v_x_327_, 1);
lean_inc(v_funIndName_329_);
v_levelMask_330_ = lean_ctor_get(v_x_327_, 2);
lean_inc_ref(v_levelMask_330_);
v_params_331_ = lean_ctor_get(v_x_327_, 3);
lean_inc_ref(v_params_331_);
lean_dec_ref(v_x_327_);
v___x_332_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5));
v___x_333_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6));
v___x_334_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = l_Lean_Name_reprPrec(v_funName_328_, v___x_335_);
v___x_337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = 0;
v___x_339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*1, v___x_338_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_333_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2));
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_box(1);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9));
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_332_);
v___x_348_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10);
v___x_349_ = l_Lean_Name_reprPrec(v_funIndName_329_, v___x_335_);
v___x_350_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*1, v___x_338_);
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_347_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_341_);
v___x_354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_343_);
v___x_355_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12));
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_332_);
v___x_358_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13);
v___x_359_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(v_levelMask_330_);
v___x_360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_338_);
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_357_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_341_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_343_);
v___x_365_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15));
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_332_);
v___x_368_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16);
v___x_369_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(v_params_331_);
v___x_370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_338_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_367_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19);
v___x_374_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20));
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_372_);
v___x_376_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21));
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_373_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*1, v___x_338_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr(lean_object* v_x_380_, lean_object* v_prec_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg(v_x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___boxed(lean_object* v_x_383_, lean_object* v_prec_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_instReprFunIndInfo_repr(v_x_383_, v_prec_384_);
lean_dec(v_prec_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(lean_object* v_env_388_, lean_object* v_as_389_, size_t v_i_390_, size_t v_stop_391_, lean_object* v_b_392_){
_start:
{
lean_object* v___y_394_; uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_eq(v_i_390_, v_stop_391_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v_fst_400_; uint8_t v___x_401_; 
v___x_399_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v_fst_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_fst_400_);
lean_inc_ref(v_env_388_);
v___x_401_ = l_Lean_Environment_contains(v_env_388_, v_fst_400_, v___x_398_);
if (v___x_401_ == 0)
{
v___y_394_ = v_b_392_;
goto v___jp_393_;
}
else
{
lean_object* v___x_402_; 
lean_inc(v___x_399_);
v___x_402_ = lean_array_push(v_b_392_, v___x_399_);
v___y_394_ = v___x_402_;
goto v___jp_393_;
}
}
else
{
lean_dec_ref(v_env_388_);
return v_b_392_;
}
v___jp_393_:
{
size_t v___x_395_; size_t v___x_396_; 
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_390_, v___x_395_);
v_i_390_ = v___x_396_;
v_b_392_ = v___y_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_403_, lean_object* v_as_404_, lean_object* v_i_405_, lean_object* v_stop_406_, lean_object* v_b_407_){
_start:
{
size_t v_i_boxed_408_; size_t v_stop_boxed_409_; lean_object* v_res_410_; 
v_i_boxed_408_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_stop_boxed_409_ = lean_unbox_usize(v_stop_406_);
lean_dec(v_stop_406_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_403_, v_as_404_, v_i_boxed_408_, v_stop_boxed_409_, v_b_407_);
lean_dec_ref(v_as_404_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_411_, lean_object* v_x_412_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v_k_413_; lean_object* v_v_414_; lean_object* v_l_415_; lean_object* v_r_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_k_413_ = lean_ctor_get(v_x_412_, 1);
v_v_414_ = lean_ctor_get(v_x_412_, 2);
v_l_415_ = lean_ctor_get(v_x_412_, 3);
v_r_416_ = lean_ctor_get(v_x_412_, 4);
v___x_417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_411_, v_l_415_);
lean_inc(v_v_414_);
lean_inc(v_k_413_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_k_413_);
lean_ctor_set(v___x_418_, 1, v_v_414_);
v___x_419_ = lean_array_push(v___x_417_, v___x_418_);
v_init_411_ = v___x_419_;
v_x_412_ = v_r_416_;
goto _start;
}
else
{
return v_init_411_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_421_, v_x_422_);
lean_dec(v_x_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(lean_object* v_env_428_, lean_object* v_s_429_, uint8_t v_x_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = ((lean_object*)(l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v___x_432_, v_s_429_);
v___x_434_ = lean_array_get_size(v___x_433_);
v___x_435_ = ((lean_object*)(l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_436_ = lean_nat_dec_lt(v___x_431_, v___x_434_);
if (v___x_436_ == 0)
{
lean_dec_ref(v___x_433_);
lean_dec_ref(v_env_428_);
return v___x_435_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_le(v___x_434_, v___x_434_);
if (v___x_437_ == 0)
{
if (v___x_436_ == 0)
{
lean_dec_ref(v___x_433_);
lean_dec_ref(v_env_428_);
return v___x_435_;
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_434_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_428_, v___x_433_, v___x_438_, v___x_439_, v___x_435_);
lean_dec_ref(v___x_433_);
return v___x_440_;
}
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_434_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_428_, v___x_433_, v___x_441_, v___x_442_, v___x_435_);
lean_dec_ref(v___x_433_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object* v_env_444_, lean_object* v_s_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_x_410__boxed_447_; lean_object* v_res_448_; 
v_x_410__boxed_447_ = lean_unbox(v_x_446_);
v_res_448_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(v_env_444_, v_s_445_, v_x_410__boxed_447_);
lean_dec(v_s_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___f_460_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_461_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_462_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_463_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_461_, v___x_462_, v___f_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(lean_object* v_init_466_, lean_object* v_t_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_466_, v_t_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_469_, lean_object* v_t_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(v_init_469_, v_t_470_);
lean_dec(v_t_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object* v_declName_478_, uint8_t v_unfolding_479_){
_start:
{
if (v_unfolding_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_getFunInductName___closed__1));
v___x_481_ = l_Lean_Name_append(v_declName_478_, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_getFunInductName___closed__3));
v___x_483_ = l_Lean_Name_append(v_declName_478_, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object* v_declName_484_, lean_object* v_unfolding_485_){
_start:
{
uint8_t v_unfolding_boxed_486_; lean_object* v_res_487_; 
v_unfolding_boxed_486_ = lean_unbox(v_unfolding_485_);
v_res_487_ = l_Lean_Meta_getFunInductName(v_declName_484_, v_unfolding_boxed_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object* v_declName_494_, uint8_t v_unfolding_495_){
_start:
{
if (v_unfolding_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_getFunCasesName___closed__1));
v___x_497_ = l_Lean_Name_append(v_declName_494_, v___x_496_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_getFunCasesName___closed__3));
v___x_499_ = l_Lean_Name_append(v_declName_494_, v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object* v_declName_500_, lean_object* v_unfolding_501_){
_start:
{
uint8_t v_unfolding_boxed_502_; lean_object* v_res_503_; 
v_unfolding_boxed_502_ = lean_unbox(v_unfolding_501_);
v_res_503_ = l_Lean_Meta_getFunCasesName(v_declName_500_, v_unfolding_boxed_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object* v_declName_510_, uint8_t v_unfolding_511_){
_start:
{
if (v_unfolding_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Meta_getMutualInductName___closed__1));
v___x_513_ = l_Lean_Name_append(v_declName_510_, v___x_512_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_getMutualInductName___closed__3));
v___x_515_ = l_Lean_Name_append(v_declName_510_, v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object* v_declName_516_, lean_object* v_unfolding_517_){
_start:
{
uint8_t v_unfolding_boxed_518_; lean_object* v_res_519_; 
v_unfolding_boxed_518_ = lean_unbox(v_unfolding_517_);
v_res_519_ = l_Lean_Meta_getMutualInductName(v_declName_516_, v_unfolding_boxed_518_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_520_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set(v___x_525_, 3, v___x_523_);
lean_ctor_set(v___x_525_, 4, v___x_523_);
lean_ctor_set(v___x_525_, 5, v___x_523_);
lean_ctor_set(v___x_525_, 6, v___x_523_);
lean_ctor_set(v___x_525_, 7, v___x_523_);
lean_ctor_set(v___x_525_, 8, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(32u);
v___x_527_ = lean_mk_empty_array_with_capacity(v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = ((size_t)5ULL);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_unsigned_to_nat(32u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_534_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_530_);
lean_ctor_set(v___x_534_, 3, v___x_530_);
lean_ctor_set_usize(v___x_534_, 4, v___x_529_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = lean_box(1);
v___x_536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_535_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_553_ = l_Lean_stringToMessageData(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_556_ = l_Lean_stringToMessageData(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_559_ = l_Lean_stringToMessageData(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_560_, lean_object* v_declHint_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v_env_565_; uint8_t v___x_566_; 
v___x_564_ = lean_st_ref_get(v___y_562_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_env_565_);
lean_dec(v___x_564_);
v___x_566_ = l_Lean_Name_isAnonymous(v_declHint_561_);
if (v___x_566_ == 0)
{
uint8_t v_isExporting_567_; 
v_isExporting_567_ = lean_ctor_get_uint8(v_env_565_, sizeof(void*)*8);
if (v_isExporting_567_ == 0)
{
lean_object* v___x_568_; 
lean_dec_ref(v_env_565_);
lean_dec(v_declHint_561_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_msg_560_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
lean_inc_ref(v_env_565_);
v___x_569_ = l_Lean_Environment_setExporting(v_env_565_, v___x_566_);
lean_inc(v_declHint_561_);
lean_inc_ref(v___x_569_);
v___x_570_ = l_Lean_Environment_contains(v___x_569_, v_declHint_561_, v_isExporting_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec_ref(v___x_569_);
lean_dec_ref(v_env_565_);
lean_dec(v_declHint_561_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v_msg_560_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_c_577_; lean_object* v___x_578_; 
v___x_572_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_573_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_574_ = l_Lean_Options_empty;
v___x_575_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_575_, 0, v___x_569_);
lean_ctor_set(v___x_575_, 1, v___x_572_);
lean_ctor_set(v___x_575_, 2, v___x_573_);
lean_ctor_set(v___x_575_, 3, v___x_574_);
lean_inc(v_declHint_561_);
v___x_576_ = l_Lean_MessageData_ofConstName(v_declHint_561_, v___x_566_);
v_c_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_577_, 0, v___x_575_);
lean_ctor_set(v_c_577_, 1, v___x_576_);
v___x_578_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_565_, v_declHint_561_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v_env_565_);
lean_dec(v_declHint_561_);
v___x_579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_c_577_);
v___x_581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_MessageData_note(v___x_582_);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v_msg_560_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v_val_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_621_; 
v_val_586_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_621_ == 0)
{
v___x_588_ = v___x_578_;
v_isShared_589_ = v_isSharedCheck_621_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_val_586_);
lean_dec(v___x_578_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_621_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_mod_593_; uint8_t v___x_594_; 
v___x_590_ = lean_box(0);
v___x_591_ = l_Lean_Environment_header(v_env_565_);
lean_dec_ref(v_env_565_);
v___x_592_ = l_Lean_EnvironmentHeader_moduleNames(v___x_591_);
v_mod_593_ = lean_array_get(v___x_590_, v___x_592_, v_val_586_);
lean_dec(v_val_586_);
lean_dec_ref(v___x_592_);
v___x_594_ = l_Lean_isPrivateName(v_declHint_561_);
lean_dec(v_declHint_561_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_c_577_);
v___x_597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_MessageData_ofName(v_mod_593_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_MessageData_note(v___x_602_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v_msg_560_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 0);
lean_ctor_set(v___x_588_, 0, v___x_604_);
v___x_606_ = v___x_588_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v_c_577_);
v___x_610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_MessageData_ofName(v_mod_593_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_MessageData_note(v___x_615_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v_msg_560_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 0);
lean_ctor_set(v___x_588_, 0, v___x_617_);
v___x_619_ = v___x_588_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_622_; 
lean_dec_ref(v_env_565_);
lean_dec(v_declHint_561_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v_msg_560_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_623_, lean_object* v_declHint_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_623_, v_declHint_624_, v___y_625_);
lean_dec(v___y_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_628_, lean_object* v_declHint_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_643_; 
v___x_633_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_628_, v_declHint_629_, v___y_631_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = l_Lean_unknownIdentifierMessageTag;
v___x_639_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_a_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_639_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_644_, lean_object* v_declHint_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_644_, v_declHint_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v_env_655_; lean_object* v_options_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_654_ = lean_st_ref_get(v___y_652_);
v_env_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_env_655_);
lean_dec(v___x_654_);
v_options_656_ = lean_ctor_get(v___y_651_, 2);
v___x_657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_658_ = lean_unsigned_to_nat(32u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
lean_dec_ref(v___x_659_);
v___x_660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_656_);
v___x_661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_661_, 0, v_env_655_);
lean_ctor_set(v___x_661_, 1, v___x_657_);
lean_ctor_set(v___x_661_, 2, v___x_660_);
lean_ctor_set(v___x_661_, 3, v_options_656_);
v___x_662_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_msgData_650_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_ref_673_; lean_object* v___x_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_ref_673_ = lean_ctor_get(v___y_670_, 5);
v___x_674_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_669_, v___y_670_, v___y_671_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_683_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc(v_ref_673_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_ref_673_);
lean_ctor_set(v___x_679_, 1, v_a_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 1);
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_fileName_694_; lean_object* v_fileMap_695_; lean_object* v_options_696_; lean_object* v_currRecDepth_697_; lean_object* v_maxRecDepth_698_; lean_object* v_ref_699_; lean_object* v_currNamespace_700_; lean_object* v_openDecls_701_; lean_object* v_initHeartbeats_702_; lean_object* v_maxHeartbeats_703_; lean_object* v_quotContext_704_; lean_object* v_currMacroScope_705_; uint8_t v_diag_706_; lean_object* v_cancelTk_x3f_707_; uint8_t v_suppressElabErrors_708_; lean_object* v_inheritedTraceOptions_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
v_fileName_694_ = lean_ctor_get(v___y_691_, 0);
v_fileMap_695_ = lean_ctor_get(v___y_691_, 1);
v_options_696_ = lean_ctor_get(v___y_691_, 2);
v_currRecDepth_697_ = lean_ctor_get(v___y_691_, 3);
v_maxRecDepth_698_ = lean_ctor_get(v___y_691_, 4);
v_ref_699_ = lean_ctor_get(v___y_691_, 5);
v_currNamespace_700_ = lean_ctor_get(v___y_691_, 6);
v_openDecls_701_ = lean_ctor_get(v___y_691_, 7);
v_initHeartbeats_702_ = lean_ctor_get(v___y_691_, 8);
v_maxHeartbeats_703_ = lean_ctor_get(v___y_691_, 9);
v_quotContext_704_ = lean_ctor_get(v___y_691_, 10);
v_currMacroScope_705_ = lean_ctor_get(v___y_691_, 11);
v_diag_706_ = lean_ctor_get_uint8(v___y_691_, sizeof(void*)*14);
v_cancelTk_x3f_707_ = lean_ctor_get(v___y_691_, 12);
v_suppressElabErrors_708_ = lean_ctor_get_uint8(v___y_691_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_709_ = lean_ctor_get(v___y_691_, 13);
v_isSharedCheck_718_ = !lean_is_exclusive(v___y_691_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v___y_691_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_inheritedTraceOptions_709_);
lean_inc(v_cancelTk_x3f_707_);
lean_inc(v_currMacroScope_705_);
lean_inc(v_quotContext_704_);
lean_inc(v_maxHeartbeats_703_);
lean_inc(v_initHeartbeats_702_);
lean_inc(v_openDecls_701_);
lean_inc(v_currNamespace_700_);
lean_inc(v_ref_699_);
lean_inc(v_maxRecDepth_698_);
lean_inc(v_currRecDepth_697_);
lean_inc(v_options_696_);
lean_inc(v_fileMap_695_);
lean_inc(v_fileName_694_);
lean_dec(v___y_691_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_ref_713_; lean_object* v___x_715_; 
v_ref_713_ = l_Lean_replaceRef(v_ref_689_, v_ref_699_);
lean_dec(v_ref_699_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 5, v_ref_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fileName_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_fileMap_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_options_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_currRecDepth_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_maxRecDepth_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_ref_713_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_currNamespace_700_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_openDecls_701_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v_initHeartbeats_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 9, v_maxHeartbeats_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 10, v_quotContext_704_);
lean_ctor_set(v_reuseFailAlloc_717_, 11, v_currMacroScope_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 12, v_cancelTk_x3f_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 13, v_inheritedTraceOptions_709_);
lean_ctor_set_uint8(v_reuseFailAlloc_717_, sizeof(void*)*14, v_diag_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_717_, sizeof(void*)*14 + 1, v_suppressElabErrors_708_);
v___x_715_ = v_reuseFailAlloc_717_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_690_, v___x_715_, v___y_692_);
lean_dec_ref(v___x_715_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_719_, lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_719_, v_msg_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec(v_ref_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v_declHint_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v_a_732_; lean_object* v___x_733_; 
v___x_731_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_726_, v_declHint_727_, v___y_728_, v___y_729_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_725_, v_a_732_, v___y_728_, v___y_729_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_734_, lean_object* v_msg_735_, lean_object* v_declHint_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_734_, v_msg_735_, v_declHint_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec(v_ref_734_);
return v_res_740_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_747_, lean_object* v_constName_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_752_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_753_ = 0;
lean_inc(v_constName_748_);
v___x_754_ = l_Lean_MessageData_ofConstName(v_constName_748_, v___x_753_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_747_, v___x_757_, v_constName_748_, v___y_749_, v___y_750_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_759_, lean_object* v_constName_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_759_, v_constName_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec(v_ref_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(lean_object* v_constName_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_ref_769_; lean_object* v___x_770_; 
v_ref_769_ = lean_ctor_get(v___y_766_, 5);
lean_inc(v_ref_769_);
v___x_770_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_769_, v_constName_765_, v___y_766_, v___y_767_);
lean_dec(v_ref_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(lean_object* v_constName_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_env_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = 0;
lean_inc(v_constName_776_);
v___x_783_ = l_Lean_Environment_find_x3f(v_env_781_, v_constName_776_, v___x_782_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_776_, v___y_777_, v___y_778_);
return v___x_784_;
}
else
{
lean_object* v_val_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v___y_777_);
lean_dec(v_constName_776_);
v_val_785_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_val_785_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set_tag(v___x_787_, 0);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0___boxed(lean_object* v_constName_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(v_constName_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t v_unfolding_798_, uint8_t v_cases_799_, lean_object* v_declName_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___x_810_; 
lean_inc_ref(v_a_801_);
lean_inc(v_declName_800_);
v___x_810_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(v_declName_800_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_836_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_836_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_836_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_836_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___y_816_; 
if (lean_obj_tag(v_a_811_) == 1)
{
lean_dec_ref(v_a_811_);
lean_del_object(v___x_813_);
if (v_cases_799_ == 0)
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_getFunInductName(v_declName_800_, v_unfolding_798_);
v___y_816_ = v___x_830_;
goto v___jp_815_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_getFunCasesName(v_declName_800_, v_unfolding_798_);
v___y_816_ = v___x_831_;
goto v___jp_815_;
}
}
else
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec(v_a_811_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_declName_800_);
v___x_832_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_832_);
v___x_834_ = v___x_813_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
v___jp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_realizeGlobalConstNoOverloadCore(v___y_816_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
else
{
lean_object* v_a_827_; uint8_t v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_817_);
v___x_828_ = l_Lean_Exception_isInterrupt(v_a_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
lean_inc(v_a_827_);
v___x_829_ = l_Lean_Exception_isRuntime(v_a_827_);
v___y_805_ = v_a_827_;
v___y_806_ = v___x_829_;
goto v___jp_804_;
}
else
{
v___y_805_ = v_a_827_;
v___y_806_ = v___x_828_;
goto v___jp_804_;
}
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_declName_800_);
v_a_837_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_810_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_810_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
v___jp_804_:
{
if (v___y_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v___y_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___y_805_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object* v_unfolding_845_, lean_object* v_cases_846_, lean_object* v_declName_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
uint8_t v_unfolding_boxed_851_; uint8_t v_cases_boxed_852_; lean_object* v_res_853_; 
v_unfolding_boxed_851_ = lean_unbox(v_unfolding_845_);
v_cases_boxed_852_ = lean_unbox(v_cases_846_);
v_res_853_ = l_Lean_Meta_getFunInduct_x3f(v_unfolding_boxed_851_, v_cases_boxed_852_, v_declName_847_, v_a_848_, v_a_849_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(lean_object* v_00_u03b1_854_, lean_object* v_constName_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_855_, v___y_856_, v___y_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_860_, lean_object* v_constName_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(v_00_u03b1_860_, v_constName_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_866_, lean_object* v_ref_867_, lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_867_, v_constName_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_873_, lean_object* v_ref_874_, lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(v_00_u03b1_873_, v_ref_874_, v_constName_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec(v_ref_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_880_, lean_object* v_ref_881_, lean_object* v_msg_882_, lean_object* v_declHint_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_881_, v_msg_882_, v_declHint_883_, v___y_884_, v___y_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_888_, lean_object* v_ref_889_, lean_object* v_msg_890_, lean_object* v_declHint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_888_, v_ref_889_, v_msg_890_, v_declHint_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec(v_ref_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_896_, lean_object* v_declHint_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_896_, v_declHint_897_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_902_, lean_object* v_declHint_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_902_, v_declHint_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_908_, lean_object* v_ref_909_, lean_object* v_msg_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_909_, v_msg_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_915_, lean_object* v_ref_916_, lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_915_, v_ref_916_, v_msg_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec(v_ref_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_922_, lean_object* v_msg_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_928_, lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_928_, v_msg_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(lean_object* v_msg_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___f_939_; lean_object* v___x_434__overap_940_; lean_object* v___x_941_; 
v___f_939_ = ((lean_object*)(l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0));
v___x_434__overap_940_ = lean_panic_fn(v___f_939_, v_msg_935_);
v___x_941_ = lean_apply_3(v___x_434__overap_940_, v___y_936_, v___y_937_, lean_box(0));
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___boxed(lean_object* v_msg_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v_msg_942_, v___y_943_, v___y_944_);
return v_res_946_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__0(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__0, &l_Lean_Meta_setFunIndInfo___closed__0_once, _init_l_Lean_Meta_setFunIndInfo___closed__0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__2(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__1, &l_Lean_Meta_setFunIndInfo___closed__1_once, _init_l_Lean_Meta_setFunIndInfo___closed__1);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__6(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__5));
v___x_956_ = lean_unsigned_to_nat(2u);
v___x_957_ = lean_unsigned_to_nat(79u);
v___x_958_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__4));
v___x_959_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__3));
v___x_960_ = l_mkPanicMessageWithDecl(v___x_959_, v___x_958_, v___x_957_, v___x_956_, v___x_955_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object* v_funIndInfo_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_env_966_; lean_object* v_funIndName_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_965_ = lean_st_ref_get(v_a_963_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_env_966_);
lean_dec(v___x_965_);
v_funIndName_967_ = lean_ctor_get(v_funIndInfo_961_, 1);
lean_inc(v_funIndName_967_);
v___x_968_ = l_Lean_Meta_instInhabitedFunIndInfo_default;
v___x_969_ = l_Lean_Meta_funIndInfoExt;
lean_inc(v_funIndName_967_);
v___x_970_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_968_, v___x_969_, v_env_966_, v_funIndName_967_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v_env_972_; lean_object* v_nextMacroScope_973_; lean_object* v_ngen_974_; lean_object* v_auxDeclNGen_975_; lean_object* v_traceState_976_; lean_object* v_messages_977_; lean_object* v_infoState_978_; lean_object* v_snapshotTasks_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_a_962_);
v___x_971_ = lean_st_ref_take(v_a_963_);
v_env_972_ = lean_ctor_get(v___x_971_, 0);
v_nextMacroScope_973_ = lean_ctor_get(v___x_971_, 1);
v_ngen_974_ = lean_ctor_get(v___x_971_, 2);
v_auxDeclNGen_975_ = lean_ctor_get(v___x_971_, 3);
v_traceState_976_ = lean_ctor_get(v___x_971_, 4);
v_messages_977_ = lean_ctor_get(v___x_971_, 6);
v_infoState_978_ = lean_ctor_get(v___x_971_, 7);
v_snapshotTasks_979_ = lean_ctor_get(v___x_971_, 8);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_971_, 5);
lean_dec(v_unused_992_);
v___x_981_ = v___x_971_;
v_isShared_982_ = v_isSharedCheck_991_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_snapshotTasks_979_);
lean_inc(v_infoState_978_);
lean_inc(v_messages_977_);
lean_inc(v_traceState_976_);
lean_inc(v_auxDeclNGen_975_);
lean_inc(v_ngen_974_);
lean_inc(v_nextMacroScope_973_);
lean_inc(v_env_972_);
lean_dec(v___x_971_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_991_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_983_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_969_, v_env_972_, v_funIndName_967_, v_funIndInfo_961_);
v___x_984_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__2, &l_Lean_Meta_setFunIndInfo___closed__2_once, _init_l_Lean_Meta_setFunIndInfo___closed__2);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 5, v___x_984_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_986_ = v___x_981_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_nextMacroScope_973_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_ngen_974_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_auxDeclNGen_975_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_traceState_976_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_990_, 6, v_messages_977_);
lean_ctor_set(v_reuseFailAlloc_990_, 7, v_infoState_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 8, v_snapshotTasks_979_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_st_ref_set(v_a_963_, v___x_986_);
lean_dec(v_a_963_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v_funIndName_967_);
lean_dec_ref(v_funIndInfo_961_);
v___x_993_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__6, &l_Lean_Meta_setFunIndInfo___closed__6_once, _init_l_Lean_Meta_setFunIndInfo___closed__6);
v___x_994_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v___x_993_, v_a_962_, v_a_963_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo___boxed(lean_object* v_funIndInfo_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_setFunIndInfo(v_funIndInfo_995_, v_a_996_, v_a_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object* v_inductName_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v_env_1004_; lean_object* v___x_1005_; lean_object* v_toEnvExtension_1006_; lean_object* v_asyncMode_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1003_ = lean_st_ref_get(v_a_1001_);
v_env_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_env_1004_);
lean_dec(v___x_1003_);
v___x_1005_ = l_Lean_Meta_funIndInfoExt;
v_toEnvExtension_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc_ref(v_toEnvExtension_1006_);
v_asyncMode_1007_ = lean_ctor_get(v_toEnvExtension_1006_, 2);
lean_inc(v_asyncMode_1007_);
lean_dec_ref(v_toEnvExtension_1006_);
v___x_1008_ = l_Lean_Meta_instInhabitedFunIndInfo_default;
v___x_1009_ = 0;
v___x_1010_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1008_, v___x_1005_, v_env_1004_, v_inductName_1000_, v_asyncMode_1007_, v___x_1009_);
lean_dec(v_asyncMode_1007_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object* v_inductName_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_1012_, v_a_1013_);
lean_dec(v_a_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object* v_inductName_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_1016_, v_a_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object* v_inductName_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_getFunIndInfoForInduct_x3f(v_inductName_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t v_cases_1026_, uint8_t v_unfolding_1027_, lean_object* v_funName_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; 
lean_inc(v_a_1030_);
v___x_1032_ = l_Lean_Meta_getFunInduct_x3f(v_unfolding_1027_, v_cases_1026_, v_funName_1028_, v_a_1029_, v_a_1030_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1043_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_a_1033_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; 
lean_del_object(v___x_1035_);
v_val_1037_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_val_1037_);
lean_dec_ref(v_a_1033_);
v___x_1038_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_val_1037_, v_a_1030_);
lean_dec(v_a_1030_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec(v_a_1033_);
lean_dec(v_a_1030_);
v___x_1039_ = lean_box(0);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1039_);
v___x_1041_ = v___x_1035_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_a_1030_);
v_a_1044_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1032_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1032_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object* v_cases_1052_, lean_object* v_unfolding_1053_, lean_object* v_funName_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
uint8_t v_cases_boxed_1058_; uint8_t v_unfolding_boxed_1059_; lean_object* v_res_1060_; 
v_cases_boxed_1058_ = lean_unbox(v_cases_1052_);
v_unfolding_boxed_1059_ = lean_unbox(v_unfolding_1053_);
v_res_1060_ = l_Lean_Meta_getFunIndInfo_x3f(v_cases_boxed_1058_, v_unfolding_boxed_1059_, v_funName_1054_, v_a_1055_, v_a_1056_);
return v_res_1060_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedFunIndParamKind_default = _init_l_Lean_Meta_instInhabitedFunIndParamKind_default();
l_Lean_Meta_instInhabitedFunIndParamKind = _init_l_Lean_Meta_instInhabitedFunIndParamKind();
l_Lean_Meta_instInhabitedFunIndInfo_default = _init_l_Lean_Meta_instInhabitedFunIndInfo_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedFunIndInfo_default);
l_Lean_Meta_instInhabitedFunIndInfo = _init_l_Lean_Meta_instInhabitedFunIndInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedFunIndInfo);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_funIndInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_funIndInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
}
#ifdef __cplusplus
}
#endif
