// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.IndGroupInfo
// Imports: public import Lean.Meta.InferType
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_instReprLevel_repr(lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkBRecOnName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instBEqIndGroupInfo = (const lean_object*)&l_Lean_Elab_Structural_instBEqIndGroupInfo___closed__0_value;
static const lean_array_object l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInfo = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10;
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst_default = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toIndGroupInfo"};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4;
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "levels"};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7;
static const lean_string_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instReprIndGroupInst = (const lean_object*)&l_Lean_Elab_Structural_instReprIndGroupInst___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_IndGroupInst_toMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instToMessageDataIndGroupInst = (const lean_object*)&l_Lean_Elab_Structural_instToMessageDataIndGroupInst___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Elab.PreDefinition.Structural.IndGroupInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Elab.Structural.IndGroupInst.nestedTypeFormers"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "assertion violation: xs.size > 0\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not a recursor"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "assertion violation: recInfo.numMotives = igi.numMotives\n  "};
static const lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1;
static const lean_array_object l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_3_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_dec(v_x_3_);
v___x_8_ = lean_array_fget_borrowed(v_xs_1_, v_n_7_);
v___x_9_ = lean_array_fget_borrowed(v_ys_2_, v_n_7_);
v___x_10_ = lean_name_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_dec(v_n_7_);
return v___x_10_;
}
else
{
v_x_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg___boxed(lean_object* v_xs_12_, lean_object* v_ys_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_xs_12_, v_ys_13_, v_x_14_);
lean_dec_ref(v_ys_13_);
lean_dec_ref(v_xs_12_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_all_19_; lean_object* v_numNested_20_; lean_object* v_all_21_; lean_object* v_numNested_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_all_19_ = lean_ctor_get(v_x_17_, 0);
v_numNested_20_ = lean_ctor_get(v_x_17_, 1);
v_all_21_ = lean_ctor_get(v_x_18_, 0);
v_numNested_22_ = lean_ctor_get(v_x_18_, 1);
v___x_23_ = lean_array_get_size(v_all_19_);
v___x_24_ = lean_array_get_size(v_all_21_);
v___x_25_ = lean_nat_dec_eq(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_all_19_, v_all_21_, v___x_23_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_numNested_20_, v_numNested_22_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_x_28_, v_x_29_);
lean_dec_ref(v_x_29_);
lean_dec_ref(v_x_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(lean_object* v_xs_32_, lean_object* v_ys_33_, lean_object* v_hsz_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_xs_32_, v_ys_33_, v_x_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___boxed(lean_object* v_xs_38_, lean_object* v_ys_39_, lean_object* v_hsz_40_, lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(v_xs_38_, v_ys_39_, v_hsz_40_, v_x_41_, v_x_42_);
lean_dec_ref(v_ys_39_);
lean_dec_ref(v_xs_38_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__1(lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_nat_to_int(v_a_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Lean_Name_reprPrec(v___y_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_dec(v_x_59_);
return v_x_60_;
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_74_; 
v_head_62_ = lean_ctor_get(v_x_61_, 0);
v_tail_63_ = lean_ctor_get(v_x_61_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v_x_61_);
if (v_isSharedCheck_74_ == 0)
{
v___x_65_ = v_x_61_;
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_tail_63_);
lean_inc(v_head_62_);
lean_dec(v_x_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
lean_inc(v_x_59_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 5);
lean_ctor_set(v___x_65_, 1, v_x_59_);
lean_ctor_set(v___x_65_, 0, v_x_60_);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_x_60_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_x_59_);
v___x_68_ = v_reuseFailAlloc_73_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = l_Lean_Name_reprPrec(v_head_62_, v___x_69_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_68_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v_x_60_ = v___x_71_;
v_x_61_ = v_tail_63_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_dec(v_x_75_);
return v_x_76_;
}
else
{
lean_object* v_head_78_; lean_object* v_tail_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_90_; 
v_head_78_ = lean_ctor_get(v_x_77_, 0);
v_tail_79_ = lean_ctor_get(v_x_77_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_x_77_);
if (v_isSharedCheck_90_ == 0)
{
v___x_81_ = v_x_77_;
v_isShared_82_ = v_isSharedCheck_90_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_tail_79_);
lean_inc(v_head_78_);
lean_dec(v_x_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_90_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
lean_inc(v_x_75_);
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 5);
lean_ctor_set(v___x_81_, 1, v_x_75_);
lean_ctor_set(v___x_81_, 0, v_x_76_);
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_x_76_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_x_75_);
v___x_84_ = v_reuseFailAlloc_89_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_Name_reprPrec(v_head_78_, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_84_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(v_x_75_, v___x_87_, v_tail_79_);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_93_; 
lean_dec(v_x_92_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v_tail_94_; 
v_tail_94_ = lean_ctor_get(v_x_91_, 1);
if (lean_obj_tag(v_tail_94_) == 0)
{
lean_object* v_head_95_; lean_object* v___x_96_; 
lean_dec(v_x_92_);
v_head_95_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_95_);
lean_dec_ref(v_x_91_);
v___x_96_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_95_);
return v___x_96_;
}
else
{
lean_object* v_head_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_inc(v_tail_94_);
v_head_97_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_97_);
lean_dec_ref(v_x_91_);
v___x_98_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_97_);
v___x_99_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(v_x_92_, v___x_98_, v_tail_94_);
return v___x_99_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0));
v___x_109_ = lean_string_length(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(lean_object* v_xs_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_array_get_size(v_xs_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_123_ = lean_array_to_list(v_xs_119_);
v___x_124_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_125_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(v___x_123_, v___x_124_);
v___x_126_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
v___x_127_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_125_);
v___x_129_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_126_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = l_Std_Format_fill(v___x_131_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; 
lean_dec_ref(v_xs_119_);
v___x_133_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10));
return v___x_133_;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(7u);
v___x_148_ = lean_nat_to_int(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(13u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0));
v___x_156_ = lean_string_length(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(lean_object* v_x_163_){
_start:
{
lean_object* v_all_164_; lean_object* v_numNested_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_199_; 
v_all_164_ = lean_ctor_get(v_x_163_, 0);
v_numNested_165_ = lean_ctor_get(v_x_163_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_199_ == 0)
{
v___x_167_ = v_x_163_;
v_isShared_168_ = v_isSharedCheck_199_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_numNested_165_);
lean_inc(v_all_164_);
lean_dec(v_x_163_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_199_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_169_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5));
v___x_170_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6));
v___x_171_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7);
v___x_172_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(v_all_164_);
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 4);
lean_ctor_set(v___x_167_, 1, v___x_172_);
lean_ctor_set(v___x_167_, 0, v___x_171_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_198_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_175_ = 0;
v___x_176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*1, v___x_175_);
v___x_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_170_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2));
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_box(1);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9));
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_169_);
v___x_185_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10);
v___x_186_ = l_Nat_reprFast(v_numNested_165_);
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_185_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_175_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_184_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13);
v___x_192_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14));
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_190_);
v___x_194_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15));
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_191_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_175_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr(lean_object* v_x_200_, lean_object* v_prec_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_x_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed(lean_object* v_x_203_, lean_object* v_prec_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr(v_x_203_, v_prec_204_);
lean_dec(v_prec_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object* v_indInfo_208_){
_start:
{
lean_object* v_all_209_; lean_object* v_numNested_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_all_209_ = lean_ctor_get(v_indInfo_208_, 3);
lean_inc(v_all_209_);
v_numNested_210_ = lean_ctor_get(v_indInfo_208_, 5);
lean_inc(v_numNested_210_);
lean_dec_ref(v_indInfo_208_);
v___x_211_ = lean_array_mk(v_all_209_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_numNested_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object* v_group_213_){
_start:
{
lean_object* v_all_214_; lean_object* v_numNested_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_all_214_ = lean_ctor_get(v_group_213_, 0);
v_numNested_215_ = lean_ctor_get(v_group_213_, 1);
v___x_216_ = lean_array_get_size(v_all_214_);
v___x_217_ = lean_nat_add(v___x_216_, v_numNested_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives___boxed(lean_object* v_group_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_group_218_);
lean_dec_ref(v_group_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object* v_info_220_, lean_object* v_idx_221_){
_start:
{
lean_object* v_all_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_all_222_ = lean_ctor_get(v_info_220_, 0);
v___x_223_ = lean_array_get_size(v_all_222_);
v___x_224_ = lean_nat_dec_lt(v_idx_221_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_j_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_225_ = lean_nat_sub(v_idx_221_, v___x_223_);
v___x_226_ = lean_unsigned_to_nat(1u);
v_j_227_ = lean_nat_add(v___x_225_, v___x_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_220_, v___x_228_);
v___x_230_ = lean_name_append_index_after(v___x_229_, v_j_227_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_array_fget_borrowed(v_all_222_, v_idx_221_);
lean_inc(v___x_231_);
v___x_232_ = l_Lean_mkBRecOnName(v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName___boxed(lean_object* v_info_233_, lean_object* v_idx_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_233_, v_idx_234_);
lean_dec(v_idx_234_);
lean_dec_ref(v_info_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_dec(v_x_242_);
return v_x_243_;
}
else
{
lean_object* v_head_245_; lean_object* v_tail_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_257_; 
v_head_245_ = lean_ctor_get(v_x_244_, 0);
v_tail_246_ = lean_ctor_get(v_x_244_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_257_ == 0)
{
v___x_248_ = v_x_244_;
v_isShared_249_ = v_isSharedCheck_257_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_tail_246_);
lean_inc(v_head_245_);
lean_dec(v_x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_257_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
lean_inc(v_x_242_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 5);
lean_ctor_set(v___x_248_, 1, v_x_242_);
lean_ctor_set(v___x_248_, 0, v_x_243_);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_x_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_x_242_);
v___x_251_ = v_reuseFailAlloc_256_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l_Lean_instReprExpr_repr(v_head_245_, v___x_252_);
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_251_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v_x_243_ = v___x_254_;
v_x_244_ = v_tail_246_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_dec(v_x_258_);
return v_x_259_;
}
else
{
lean_object* v_head_261_; lean_object* v_tail_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_273_; 
v_head_261_ = lean_ctor_get(v_x_260_, 0);
v_tail_262_ = lean_ctor_get(v_x_260_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_273_ == 0)
{
v___x_264_ = v_x_260_;
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_tail_262_);
lean_inc(v_head_261_);
lean_dec(v_x_260_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
lean_inc(v_x_258_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 5);
lean_ctor_set(v___x_264_, 1, v_x_258_);
lean_ctor_set(v___x_264_, 0, v_x_259_);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_x_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_x_258_);
v___x_267_ = v_reuseFailAlloc_272_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Lean_instReprExpr_repr(v_head_261_, v___x_268_);
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_267_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(v_x_258_, v___x_270_, v_tail_262_);
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(lean_object* v___y_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = l_Lean_instReprExpr_repr(v___y_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_279_; 
lean_dec(v_x_278_);
v___x_279_ = lean_box(0);
return v___x_279_;
}
else
{
lean_object* v_tail_280_; 
v_tail_280_ = lean_ctor_get(v_x_277_, 1);
if (lean_obj_tag(v_tail_280_) == 0)
{
lean_object* v_head_281_; lean_object* v___x_282_; 
lean_dec(v_x_278_);
v_head_281_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_head_281_);
lean_dec_ref(v_x_277_);
v___x_282_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_281_);
return v___x_282_;
}
else
{
lean_object* v_head_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
lean_inc(v_tail_280_);
v_head_283_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_head_283_);
lean_dec_ref(v_x_277_);
v___x_284_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_283_);
v___x_285_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(v_x_278_, v___x_284_, v_tail_280_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(lean_object* v_xs_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = lean_array_get_size(v_xs_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_290_ = lean_array_to_list(v_xs_286_);
v___x_291_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_292_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(v___x_290_, v___x_291_);
v___x_293_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
v___x_294_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_292_);
v___x_296_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_293_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Std_Format_fill(v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v_xs_286_);
v___x_300_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10));
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_dec(v_x_301_);
return v_x_302_;
}
else
{
lean_object* v_head_304_; lean_object* v_tail_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_316_; 
v_head_304_ = lean_ctor_get(v_x_303_, 0);
v_tail_305_ = lean_ctor_get(v_x_303_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_316_ == 0)
{
v___x_307_ = v_x_303_;
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_tail_305_);
lean_inc(v_head_304_);
lean_dec(v_x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
lean_inc(v_x_301_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 5);
lean_ctor_set(v___x_307_, 1, v_x_301_);
lean_ctor_set(v___x_307_, 0, v_x_302_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_x_301_);
v___x_310_ = v_reuseFailAlloc_315_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Lean_instReprLevel_repr(v_head_304_, v___x_311_);
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_310_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v_x_302_ = v___x_313_;
v_x_303_ = v_tail_305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_dec(v_x_317_);
return v_x_318_;
}
else
{
lean_object* v_head_320_; lean_object* v_tail_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
v_head_320_ = lean_ctor_get(v_x_319_, 0);
v_tail_321_ = lean_ctor_get(v_x_319_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_332_ == 0)
{
v___x_323_ = v_x_319_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_tail_321_);
lean_inc(v_head_320_);
lean_dec(v_x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
lean_inc(v_x_317_);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 5);
lean_ctor_set(v___x_323_, 1, v_x_317_);
lean_ctor_set(v___x_323_, 0, v_x_318_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_x_318_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_x_317_);
v___x_326_ = v_reuseFailAlloc_331_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_Lean_instReprLevel_repr(v_head_320_, v___x_327_);
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_326_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(v_x_317_, v___x_329_, v_tail_321_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(lean_object* v___y_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = l_Lean_instReprLevel_repr(v___y_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_338_; 
lean_dec(v_x_337_);
v___x_338_ = lean_box(0);
return v___x_338_;
}
else
{
lean_object* v_tail_339_; 
v_tail_339_ = lean_ctor_get(v_x_336_, 1);
if (lean_obj_tag(v_tail_339_) == 0)
{
lean_object* v_head_340_; lean_object* v___x_341_; 
lean_dec(v_x_337_);
v_head_340_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_head_340_);
lean_dec_ref(v_x_336_);
v___x_341_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_340_);
return v___x_341_;
}
else
{
lean_object* v_head_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_inc(v_tail_339_);
v_head_342_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_head_342_);
lean_dec_ref(v_x_336_);
v___x_343_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_342_);
v___x_344_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(v_x_337_, v___x_343_, v_tail_339_);
return v___x_344_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2));
v___x_350_ = lean_string_length(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3, &l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3);
v___x_352_ = lean_nat_to_int(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(lean_object* v_a_355_){
_start:
{
if (lean_obj_tag(v_a_355_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1));
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; 
v___x_357_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_358_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(v_a_355_, v___x_357_);
v___x_359_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4);
v___x_360_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5));
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_358_);
v___x_362_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_359_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = 0;
v___x_366_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_365_);
return v___x_366_;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(18u);
v___x_377_ = lean_nat_to_int(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(10u);
v___x_382_ = lean_nat_to_int(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(lean_object* v_x_386_){
_start:
{
lean_object* v_toIndGroupInfo_387_; lean_object* v_levels_388_; lean_object* v_params_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_toIndGroupInfo_387_ = lean_ctor_get(v_x_386_, 0);
lean_inc_ref(v_toIndGroupInfo_387_);
v_levels_388_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_levels_388_);
v_params_389_ = lean_ctor_get(v_x_386_, 2);
lean_inc_ref(v_params_389_);
lean_dec_ref(v_x_386_);
v___x_390_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5));
v___x_391_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3));
v___x_392_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4, &l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once, _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4);
v___x_393_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_toIndGroupInfo_387_);
v___x_394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = 0;
v___x_396_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*1, v___x_395_);
v___x_397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_391_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2));
v___x_399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_box(1);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6));
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_390_);
v___x_405_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7, &l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once, _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7);
v___x_406_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(v_levels_388_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*1, v___x_395_);
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_404_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_398_);
v___x_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_400_);
v___x_412_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9));
v___x_413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_390_);
v___x_415_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(v_params_389_);
v___x_416_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_405_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_395_);
v___x_418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_414_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13);
v___x_420_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14));
v___x_421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_418_);
v___x_422_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15));
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_419_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_395_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr(lean_object* v_x_426_, lean_object* v_prec_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed(lean_object* v_x_429_, lean_object* v_prec_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr(v_x_429_, v_prec_430_);
lean_dec(v_prec_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(lean_object* v_a_432_, lean_object* v_n_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(v_a_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___boxed(lean_object* v_a_435_, lean_object* v_n_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(v_a_435_, v_n_436_);
lean_dec(v_n_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object* v_igi_440_){
_start:
{
lean_object* v_toIndGroupInfo_441_; lean_object* v_levels_442_; lean_object* v_params_443_; lean_object* v_all_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_toIndGroupInfo_441_ = lean_ctor_get(v_igi_440_, 0);
lean_inc_ref(v_toIndGroupInfo_441_);
v_levels_442_ = lean_ctor_get(v_igi_440_, 1);
lean_inc(v_levels_442_);
v_params_443_ = lean_ctor_get(v_igi_440_, 2);
lean_inc_ref(v_params_443_);
lean_dec_ref(v_igi_440_);
v_all_444_ = lean_ctor_get(v_toIndGroupInfo_441_, 0);
lean_inc_ref(v_all_444_);
lean_dec_ref(v_toIndGroupInfo_441_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_array_get(v___x_445_, v_all_444_, v___x_446_);
lean_dec_ref(v_all_444_);
v___x_448_ = l_Lean_Expr_const___override(v___x_447_, v_levels_442_);
v___x_449_ = l_Lean_mkAppN(v___x_448_, v_params_443_);
lean_dec_ref(v_params_443_);
v___x_450_ = l_Lean_MessageData_ofExpr(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(lean_object* v_x_453_){
_start:
{
lean_object* v_fst_454_; lean_object* v_snd_455_; uint8_t v___x_456_; 
v_fst_454_ = lean_ctor_get(v_x_453_, 0);
v_snd_455_ = lean_ctor_get(v_x_453_, 1);
v___x_456_ = l_Lean_Level_isEquiv(v_fst_454_, v_snd_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed(lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(v_x_457_);
lean_dec_ref(v_x_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(uint8_t v___x_460_, uint8_t v_____do__lift_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
if (v_____do__lift_461_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_box(v___x_460_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
else
{
uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = 0;
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1___boxed(lean_object* v___x_472_, lean_object* v_____do__lift_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v___x_2311__boxed_479_; uint8_t v_____do__lift_2312__boxed_480_; lean_object* v_res_481_; 
v___x_2311__boxed_479_ = lean_unbox(v___x_472_);
v_____do__lift_2312__boxed_480_ = lean_unbox(v_____do__lift_473_);
v_res_481_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(v___x_2311__boxed_479_, v_____do__lift_2312__boxed_480_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(uint8_t v___x_482_, lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; uint8_t v___x_495_; uint8_t v_a_497_; lean_object* v___x_503_; 
v___x_492_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
v_fst_493_ = lean_ctor_get(v___x_492_, 0);
v_snd_494_ = lean_ctor_get(v___x_492_, 1);
v___x_495_ = 1;
lean_inc(v_snd_494_);
lean_inc(v_fst_493_);
v___x_503_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_493_, v_snd_494_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; uint8_t v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_505_ == 0)
{
v_a_497_ = v___x_482_;
goto v___jp_496_;
}
else
{
v_a_497_ = v___x_491_;
goto v___jp_496_;
}
}
else
{
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_506_; uint8_t v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_503_);
v___x_507_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
v_a_497_ = v___x_507_;
goto v___jp_496_;
}
else
{
return v___x_503_;
}
}
v___jp_496_:
{
if (v_a_497_ == 0)
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_484_, v___x_498_);
v_i_484_ = v___x_499_;
goto _start;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(v___x_495_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
else
{
uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = 0;
v___x_509_ = lean_box(v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(lean_object* v___x_511_, lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_stop_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v___x_2342__boxed_520_; size_t v_i_boxed_521_; size_t v_stop_boxed_522_; lean_object* v_res_523_; 
v___x_2342__boxed_520_ = lean_unbox(v___x_511_);
v_i_boxed_521_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_stop_boxed_522_ = lean_unbox_usize(v_stop_514_);
lean_dec(v_stop_514_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v___x_2342__boxed_520_, v_as_512_, v_i_boxed_521_, v_stop_boxed_522_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_as_512_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object* v_igi1_525_, lean_object* v_igi2_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_toIndGroupInfo_532_; lean_object* v_levels_533_; lean_object* v_params_534_; lean_object* v_toIndGroupInfo_535_; lean_object* v_levels_536_; lean_object* v_params_537_; uint8_t v___x_538_; 
v_toIndGroupInfo_532_ = lean_ctor_get(v_igi1_525_, 0);
lean_inc_ref(v_toIndGroupInfo_532_);
v_levels_533_ = lean_ctor_get(v_igi1_525_, 1);
lean_inc(v_levels_533_);
v_params_534_ = lean_ctor_get(v_igi1_525_, 2);
lean_inc_ref(v_params_534_);
lean_dec_ref(v_igi1_525_);
v_toIndGroupInfo_535_ = lean_ctor_get(v_igi2_526_, 0);
lean_inc_ref(v_toIndGroupInfo_535_);
v_levels_536_ = lean_ctor_get(v_igi2_526_, 1);
lean_inc(v_levels_536_);
v_params_537_ = lean_ctor_get(v_igi2_526_, 2);
lean_inc_ref(v_params_537_);
lean_dec_ref(v_igi2_526_);
v___x_538_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_toIndGroupInfo_532_, v_toIndGroupInfo_535_);
lean_dec_ref(v_toIndGroupInfo_535_);
lean_dec_ref(v_toIndGroupInfo_532_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v_params_537_);
lean_dec(v_levels_536_);
lean_dec_ref(v_params_534_);
lean_dec(v_levels_533_);
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_541_ = l_List_lengthTR___redArg(v_levels_533_);
v___x_542_ = l_List_lengthTR___redArg(v_levels_536_);
v___x_543_ = lean_nat_dec_eq(v___x_541_, v___x_542_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v_params_537_);
lean_dec(v_levels_536_);
lean_dec_ref(v_params_534_);
lean_dec(v_levels_533_);
v___x_544_ = lean_box(v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v___f_546_; lean_object* v___x_547_; uint8_t v___x_548_; uint8_t v_a_550_; lean_object* v___y_556_; 
v___f_546_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0));
v___x_547_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_levels_533_, v_levels_536_);
v___x_548_ = l_List_all___redArg(v___x_547_, v___f_546_);
if (v___x_548_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v_params_537_);
lean_dec_ref(v_params_534_);
v___x_559_ = lean_box(v___x_548_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_array_get_size(v_params_534_);
v___x_562_ = lean_array_get_size(v_params_537_);
v___x_563_ = lean_nat_dec_eq(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_params_537_);
lean_dec_ref(v_params_534_);
v___x_564_ = lean_box(v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_566_ = l_Array_zip___redArg(v_params_534_, v_params_537_);
lean_dec_ref(v_params_537_);
lean_dec_ref(v_params_534_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_get_size(v___x_566_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec_ref(v___x_566_);
v___x_570_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(v___x_548_, v___x_569_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
v___y_556_ = v___x_570_;
goto v___jp_555_;
}
else
{
if (v___x_569_ == 0)
{
lean_dec_ref(v___x_566_);
v_a_550_ = v___x_548_;
goto v___jp_549_;
}
else
{
size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v___x_571_ = ((size_t)0ULL);
v___x_572_ = lean_usize_of_nat(v___x_568_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v___x_548_, v___x_566_, v___x_571_, v___x_572_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec_ref(v___x_566_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; uint8_t v___x_575_; lean_object* v___x_576_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_573_);
v___x_575_ = lean_unbox(v_a_574_);
lean_dec(v_a_574_);
v___x_576_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(v___x_548_, v___x_575_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
v___y_556_ = v___x_576_;
goto v___jp_555_;
}
else
{
v___y_556_ = v___x_573_;
goto v___jp_555_;
}
}
}
}
}
v___jp_549_:
{
if (v_a_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box(v_a_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_box(v___x_548_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
v___jp_555_:
{
if (lean_obj_tag(v___y_556_) == 0)
{
lean_object* v_a_557_; uint8_t v___x_558_; 
v_a_557_ = lean_ctor_get(v___y_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref(v___y_556_);
v___x_558_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
v_a_550_ = v___x_558_;
goto v___jp_549_;
}
else
{
return v___y_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(lean_object* v_igi1_577_, lean_object* v_igi2_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_igi1_577_, v_igi2_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn(lean_object* v_group_585_, lean_object* v_lvl_586_, lean_object* v_idx_587_){
_start:
{
lean_object* v_toIndGroupInfo_588_; lean_object* v_levels_589_; lean_object* v_params_590_; lean_object* v_n_591_; lean_object* v_us_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_toIndGroupInfo_588_ = lean_ctor_get(v_group_585_, 0);
v_levels_589_ = lean_ctor_get(v_group_585_, 1);
v_params_590_ = lean_ctor_get(v_group_585_, 2);
v_n_591_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_588_, v_idx_587_);
lean_inc(v_levels_589_);
v_us_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_592_, 0, v_lvl_586_);
lean_ctor_set(v_us_592_, 1, v_levels_589_);
v___x_593_ = l_Lean_Expr_const___override(v_n_591_, v_us_592_);
v___x_594_ = l_Lean_mkAppN(v___x_593_, v_params_590_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(lean_object* v_group_595_, lean_object* v_lvl_596_, lean_object* v_idx_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_Structural_IndGroupInst_brecOn(v_group_595_, v_lvl_596_, v_idx_597_);
lean_dec(v_idx_597_);
lean_dec_ref(v_group_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___f_606_; lean_object* v___x_988__overap_607_; lean_object* v___x_608_; 
v___f_606_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0));
v___x_988__overap_607_ = lean_panic_fn_borrowed(v___f_606_, v_msg_600_);
lean_inc(v___y_604_);
lean_inc_ref(v___y_603_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
v___x_608_ = lean_apply_5(v___x_988__overap_607_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, lean_box(0));
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___boxed(lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(lean_object* v_k_616_, lean_object* v_b_617_, lean_object* v_c_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; 
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
v___x_624_ = lean_apply_7(v_k_616_, v_b_617_, v_c_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, lean_box(0));
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed(lean_object* v_k_625_, lean_object* v_b_626_, lean_object* v_c_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(v_k_625_, v_b_626_, v_c_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(lean_object* v_type_634_, lean_object* v_k_635_, uint8_t v_cleanupAnnotations_636_, uint8_t v_whnfType_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___f_643_; lean_object* v___x_644_; 
v___f_643_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_643_, 0, v_k_635_);
v___x_644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_634_, v___f_643_, v_cleanupAnnotations_636_, v_whnfType_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
v_a_653_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_644_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_644_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___boxed(lean_object* v_type_661_, lean_object* v_k_662_, lean_object* v_cleanupAnnotations_663_, lean_object* v_whnfType_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_670_; uint8_t v_whnfType_boxed_671_; lean_object* v_res_672_; 
v_cleanupAnnotations_boxed_670_ = lean_unbox(v_cleanupAnnotations_663_);
v_whnfType_boxed_671_ = lean_unbox(v_whnfType_664_);
v_res_672_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_661_, v_k_662_, v_cleanupAnnotations_boxed_670_, v_whnfType_boxed_671_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(lean_object* v_00_u03b1_673_, lean_object* v_type_674_, lean_object* v_k_675_, uint8_t v_cleanupAnnotations_676_, uint8_t v_whnfType_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_674_, v_k_675_, v_cleanupAnnotations_676_, v_whnfType_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___boxed(lean_object* v_00_u03b1_684_, lean_object* v_type_685_, lean_object* v_k_686_, lean_object* v_cleanupAnnotations_687_, lean_object* v_whnfType_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_694_; uint8_t v_whnfType_boxed_695_; lean_object* v_res_696_; 
v_cleanupAnnotations_boxed_694_ = lean_unbox(v_cleanupAnnotations_687_);
v_whnfType_boxed_695_ = lean_unbox(v_whnfType_688_);
v_res_696_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(v_00_u03b1_684_, v_type_685_, v_k_686_, v_cleanupAnnotations_boxed_694_, v_whnfType_boxed_695_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___f_703_; lean_object* v___x_2050__overap_704_; lean_object* v___x_705_; 
v___f_703_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0));
v___x_2050__overap_704_ = lean_panic_fn_borrowed(v___f_703_, v_msg_697_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_705_ = lean_apply_5(v___x_2050__overap_704_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4___boxed(lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v_msg_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2));
v___x_717_ = lean_unsigned_to_nat(6u);
v___x_718_ = lean_unsigned_to_nat(113u);
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1));
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0));
v___x_721_ = l_mkPanicMessageWithDecl(v___x_720_, v___x_719_, v___x_718_, v___x_717_, v___x_716_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(lean_object* v___x_722_, lean_object* v_xs_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_xs_723_);
v___x_731_ = lean_nat_dec_lt(v___x_722_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_xs_723_);
v___x_732_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3);
v___x_733_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v___x_732_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_734_ = l_Lean_instInhabitedExpr;
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_sub(v___x_730_, v___x_735_);
v___x_737_ = lean_array_get_borrowed(v___x_734_, v_xs_723_, v___x_736_);
lean_dec(v___x_736_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___x_737_);
v___x_738_ = lean_infer_type(v___x_737_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = lean_array_pop(v_xs_723_);
v___x_741_ = 0;
v___x_742_ = 1;
v___x_743_ = l_Lean_Meta_mkForallFVars(v___x_740_, v_a_739_, v___x_741_, v___x_731_, v___x_731_, v___x_742_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec_ref(v___x_740_);
return v___x_743_;
}
else
{
lean_dec_ref(v_xs_723_);
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(lean_object* v___x_744_, lean_object* v_xs_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(v___x_744_, v_xs_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_x_746_);
lean_dec(v___x_744_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(size_t v_sz_755_, size_t v_i_756_, lean_object* v_bs_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = lean_usize_dec_lt(v_i_756_, v_sz_755_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v_bs_757_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v_v_767_; uint8_t v___x_768_; lean_object* v___x_769_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___f_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___closed__0));
v_v_767_ = lean_array_uget_borrowed(v_bs_757_, v_i_756_);
v___x_768_ = 0;
lean_inc(v_v_767_);
v___x_769_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_v_767_, v___f_766_, v___x_768_, v___x_768_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_bs_x27_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v_bs_x27_771_ = lean_array_uset(v_bs_757_, v_i_756_, v___x_765_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_756_, v___x_772_);
v___x_774_ = lean_array_uset(v_bs_x27_771_, v_i_756_, v_a_770_);
v_i_756_ = v___x_773_;
v_bs_757_ = v___x_774_;
goto _start;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_bs_757_);
v_a_776_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_769_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___boxed(lean_object* v_sz_784_, lean_object* v_i_785_, lean_object* v_bs_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
size_t v_sz_boxed_792_; size_t v_i_boxed_793_; lean_object* v_res_794_; 
v_sz_boxed_792_ = lean_unbox_usize(v_sz_784_);
lean_dec(v_sz_784_);
v_i_boxed_793_ = lean_unbox_usize(v_i_785_);
lean_dec(v_i_785_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_sz_boxed_792_, v_i_boxed_793_, v_bs_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_794_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_instMonadEIO(lean_box(0));
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_toApplicative_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_869_; 
v___x_806_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0);
v___x_807_ = l_StateRefT_x27_instMonad___redArg(v___x_806_);
v_toApplicative_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v___x_807_, 1);
lean_dec(v_unused_870_);
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_869_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_toApplicative_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_869_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_toFunctor_812_; lean_object* v_toSeq_813_; lean_object* v_toSeqLeft_814_; lean_object* v_toSeqRight_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_867_; 
v_toFunctor_812_ = lean_ctor_get(v_toApplicative_808_, 0);
v_toSeq_813_ = lean_ctor_get(v_toApplicative_808_, 2);
v_toSeqLeft_814_ = lean_ctor_get(v_toApplicative_808_, 3);
v_toSeqRight_815_ = lean_ctor_get(v_toApplicative_808_, 4);
v_isSharedCheck_867_ = !lean_is_exclusive(v_toApplicative_808_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_toApplicative_808_, 1);
lean_dec(v_unused_868_);
v___x_817_ = v_toApplicative_808_;
v_isShared_818_ = v_isSharedCheck_867_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_toSeqRight_815_);
lean_inc(v_toSeqLeft_814_);
lean_inc(v_toSeq_813_);
lean_inc(v_toFunctor_812_);
lean_dec(v_toApplicative_808_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_867_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___x_828_; 
v___f_819_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1));
v___f_820_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_812_);
v___f_821_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_821_, 0, v_toFunctor_812_);
v___f_822_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_822_, 0, v_toFunctor_812_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___f_821_);
lean_ctor_set(v___x_823_, 1, v___f_822_);
v___f_824_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_824_, 0, v_toSeqRight_815_);
v___f_825_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_825_, 0, v_toSeqLeft_814_);
v___f_826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_826_, 0, v_toSeq_813_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 4, v___f_824_);
lean_ctor_set(v___x_817_, 3, v___f_825_);
lean_ctor_set(v___x_817_, 2, v___f_826_);
lean_ctor_set(v___x_817_, 1, v___f_819_);
lean_ctor_set(v___x_817_, 0, v___x_823_);
v___x_828_ = v___x_817_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___f_819_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v___f_826_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v___f_825_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v___f_824_);
v___x_828_ = v_reuseFailAlloc_866_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v___f_820_);
lean_ctor_set(v___x_810_, 0, v___x_828_);
v___x_830_ = v___x_810_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___f_820_);
v___x_830_ = v_reuseFailAlloc_865_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v_toApplicative_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_863_; 
v___x_831_ = l_StateRefT_x27_instMonad___redArg(v___x_830_);
v_toApplicative_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_831_, 1);
lean_dec(v_unused_864_);
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_863_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_toApplicative_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_863_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_toFunctor_836_; lean_object* v_toSeq_837_; lean_object* v_toSeqLeft_838_; lean_object* v_toSeqRight_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_861_; 
v_toFunctor_836_ = lean_ctor_get(v_toApplicative_832_, 0);
v_toSeq_837_ = lean_ctor_get(v_toApplicative_832_, 2);
v_toSeqLeft_838_ = lean_ctor_get(v_toApplicative_832_, 3);
v_toSeqRight_839_ = lean_ctor_get(v_toApplicative_832_, 4);
v_isSharedCheck_861_ = !lean_is_exclusive(v_toApplicative_832_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_toApplicative_832_, 1);
lean_dec(v_unused_862_);
v___x_841_ = v_toApplicative_832_;
v_isShared_842_ = v_isSharedCheck_861_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_toSeqRight_839_);
lean_inc(v_toSeqLeft_838_);
lean_inc(v_toSeq_837_);
lean_inc(v_toFunctor_836_);
lean_dec(v_toApplicative_832_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_861_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_852_; 
v___f_843_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3));
v___f_844_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_836_);
v___f_845_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_845_, 0, v_toFunctor_836_);
v___f_846_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_846_, 0, v_toFunctor_836_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___f_845_);
lean_ctor_set(v___x_847_, 1, v___f_846_);
v___f_848_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_848_, 0, v_toSeqRight_839_);
v___f_849_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_849_, 0, v_toSeqLeft_838_);
v___f_850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_850_, 0, v_toSeq_837_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 4, v___f_848_);
lean_ctor_set(v___x_841_, 3, v___f_849_);
lean_ctor_set(v___x_841_, 2, v___f_850_);
lean_ctor_set(v___x_841_, 1, v___f_843_);
lean_ctor_set(v___x_841_, 0, v___x_847_);
v___x_852_ = v___x_841_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___f_843_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v___f_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v___f_849_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v___f_848_);
v___x_852_ = v_reuseFailAlloc_860_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___f_844_);
lean_ctor_set(v___x_834_, 0, v___x_852_);
v___x_854_ = v___x_834_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___f_844_);
v___x_854_ = v_reuseFailAlloc_859_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_2651__overap_857_; lean_object* v___x_858_; 
v___x_855_ = lean_box(0);
v___x_856_ = l_instInhabitedOfMonad___redArg(v___x_854_, v___x_855_);
v___x_2651__overap_857_ = lean_panic_fn_borrowed(v___x_856_, v_msg_800_);
lean_dec(v___x_856_);
lean_inc(v___y_804_);
lean_inc_ref(v___y_803_);
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
v___x_858_ = lean_apply_5(v___x_2651__overap_857_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, lean_box(0));
return v___x_858_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___boxed(lean_object* v_msg_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v_msg_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_env_885_; lean_object* v___x_886_; lean_object* v_mctx_887_; lean_object* v_lctx_888_; lean_object* v_options_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_884_ = lean_st_ref_get(v___y_882_);
v_env_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_884_);
v___x_886_ = lean_st_ref_get(v___y_880_);
v_mctx_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_mctx_887_);
lean_dec(v___x_886_);
v_lctx_888_ = lean_ctor_get(v___y_879_, 2);
v_options_889_ = lean_ctor_get(v___y_881_, 2);
lean_inc_ref(v_options_889_);
lean_inc_ref(v_lctx_888_);
v___x_890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_890_, 0, v_env_885_);
lean_ctor_set(v___x_890_, 1, v_mctx_887_);
lean_ctor_set(v___x_890_, 2, v_lctx_888_);
lean_ctor_set(v___x_890_, 3, v_options_889_);
v___x_891_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_msgData_878_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msgData_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_ref_906_ = lean_ctor_get(v___y_903_, 5);
v___x_907_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_inc(v_ref_906_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_ref_906_);
lean_ctor_set(v___x_912_, 1, v_a_908_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 1);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg___boxed(lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_933_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6));
v___x_934_ = lean_unsigned_to_nat(11u);
v___x_935_ = lean_unsigned_to_nat(129u);
v___x_936_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5));
v___x_937_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4));
v___x_938_ = l_mkPanicMessageWithDecl(v___x_937_, v___x_936_, v___x_935_, v___x_934_, v___x_933_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(lean_object* v_constName_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_953_; lean_object* v_env_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v___x_953_ = lean_st_ref_get(v___y_943_);
v_env_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc_ref(v_env_954_);
lean_dec(v___x_953_);
v___x_955_ = 0;
lean_inc(v_constName_939_);
v___x_956_ = l_Lean_Environment_findAsync_x3f(v_env_954_, v_constName_939_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; uint8_t v_kind_958_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref(v___x_956_);
v_kind_958_ = lean_ctor_get_uint8(v_val_957_, sizeof(void*)*3);
if (v_kind_958_ == 7)
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_957_);
if (lean_obj_tag(v___x_959_) == 7)
{
lean_object* v_val_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_constName_939_);
v_val_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_val_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 0);
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_val_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec_ref(v___x_959_);
v___x_968_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7);
v___x_969_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v___x_968_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
if (lean_obj_tag(v_a_970_) == 0)
{
lean_del_object(v___x_972_);
goto v___jp_945_;
}
else
{
lean_object* v_val_974_; lean_object* v___x_976_; 
lean_dec(v_constName_939_);
v_val_974_ = lean_ctor_get(v_a_970_, 0);
lean_inc(v_val_974_);
lean_dec_ref(v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v_val_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_val_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_constName_939_);
v_a_979_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_969_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_969_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
else
{
lean_dec(v_val_957_);
goto v___jp_945_;
}
}
else
{
lean_dec(v___x_956_);
goto v___jp_945_;
}
v___jp_945_:
{
lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_946_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1);
v___x_947_ = 0;
v___x_948_ = l_Lean_MessageData_ofConstName(v_constName_939_, v___x_947_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_946_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v___x_951_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___boxed(lean_object* v_constName_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_constName_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_995_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0));
v___x_996_ = lean_unsigned_to_nat(2u);
v___x_997_ = lean_unsigned_to_nat(104u);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1));
v___x_999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0));
v___x_1000_ = l_mkPanicMessageWithDecl(v___x_999_, v___x_998_, v___x_997_, v___x_996_, v___x_995_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object* v_igi_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___y_1010_; lean_object* v_lower_1011_; lean_object* v_upper_1012_; lean_object* v_toIndGroupInfo_1018_; lean_object* v_levels_1019_; lean_object* v_params_1020_; lean_object* v_all_1021_; lean_object* v_numNested_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_toIndGroupInfo_1018_ = lean_ctor_get(v_igi_1003_, 0);
lean_inc_ref(v_toIndGroupInfo_1018_);
v_levels_1019_ = lean_ctor_get(v_igi_1003_, 1);
lean_inc(v_levels_1019_);
v_params_1020_ = lean_ctor_get(v_igi_1003_, 2);
lean_inc_ref(v_params_1020_);
lean_dec_ref(v_igi_1003_);
v_all_1021_ = lean_ctor_get(v_toIndGroupInfo_1018_, 0);
lean_inc_ref(v_all_1021_);
v_numNested_1022_ = lean_ctor_get(v_toIndGroupInfo_1018_, 1);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_nat_dec_eq(v_numNested_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_recName_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_array_get_borrowed(v___x_1025_, v_all_1021_, v___x_1023_);
lean_inc(v___x_1026_);
v_recName_1027_ = l_Lean_mkRecName(v___x_1026_);
lean_inc(v_recName_1027_);
v___x_1028_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_recName_1027_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_toConstantVal_1030_; lean_object* v_numMotives_1031_; lean_object* v___y_1033_; lean_object* v___x_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1056_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v_toConstantVal_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc_ref(v_toConstantVal_1030_);
v_numMotives_1031_ = lean_ctor_get(v_a_1029_, 4);
lean_inc(v_numMotives_1031_);
lean_dec(v_a_1029_);
v___x_1041_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_1018_);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_toIndGroupInfo_1018_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; lean_object* v_unused_1058_; 
v_unused_1057_ = lean_ctor_get(v_toIndGroupInfo_1018_, 1);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_toIndGroupInfo_1018_, 0);
lean_dec(v_unused_1058_);
v___x_1043_ = v_toIndGroupInfo_1018_;
v_isShared_1044_ = v_isSharedCheck_1056_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v_toIndGroupInfo_1018_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1056_;
goto v_resetjp_1042_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = l_Lean_Expr_const___override(v_recName_1027_, v___y_1033_);
v___x_1035_ = l_Lean_mkAppN(v___x_1034_, v_params_1020_);
lean_dec_ref(v_params_1020_);
v___x_1036_ = l_Lean_Meta_inferArgumentTypesN(v_numMotives_1031_, v___x_1035_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = lean_array_get_size(v_all_1021_);
lean_dec_ref(v_all_1021_);
v___x_1039_ = lean_array_get_size(v_a_1037_);
v___x_1040_ = lean_nat_dec_le(v___x_1038_, v___x_1023_);
if (v___x_1040_ == 0)
{
v___y_1010_ = v_a_1037_;
v_lower_1011_ = v___x_1038_;
v_upper_1012_ = v___x_1039_;
goto v___jp_1009_;
}
else
{
v___y_1010_ = v_a_1037_;
v_lower_1011_ = v___x_1023_;
v_upper_1012_ = v___x_1039_;
goto v___jp_1009_;
}
}
else
{
lean_dec_ref(v_all_1021_);
return v___x_1036_;
}
}
v_resetjp_1042_:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_nat_dec_eq(v_numMotives_1031_, v___x_1041_);
lean_dec(v___x_1041_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1043_);
lean_dec(v_numMotives_1031_);
lean_dec_ref(v_toConstantVal_1030_);
lean_dec(v_recName_1027_);
lean_dec_ref(v_all_1021_);
lean_dec_ref(v_params_1020_);
lean_dec(v_levels_1019_);
v___x_1046_ = lean_obj_once(&l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1, &l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once, _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1);
v___x_1047_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v___x_1046_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1047_;
}
else
{
lean_object* v_levelParams_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_levelParams_1048_ = lean_ctor_get(v_toConstantVal_1030_, 1);
lean_inc(v_levelParams_1048_);
lean_dec_ref(v_toConstantVal_1030_);
v___x_1049_ = l_List_lengthTR___redArg(v_levels_1019_);
v___x_1050_ = l_List_lengthTR___redArg(v_levelParams_1048_);
lean_dec(v_levelParams_1048_);
v___x_1051_ = lean_nat_dec_eq(v___x_1049_, v___x_1050_);
lean_dec(v___x_1050_);
lean_dec(v___x_1049_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_box(0);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
lean_ctor_set(v___x_1043_, 1, v_levels_1019_);
lean_ctor_set(v___x_1043_, 0, v___x_1052_);
v___x_1054_ = v___x_1043_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_levels_1019_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
v___y_1033_ = v___x_1054_;
goto v___jp_1032_;
}
}
else
{
lean_del_object(v___x_1043_);
v___y_1033_ = v_levels_1019_;
goto v___jp_1032_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_recName_1027_);
lean_dec_ref(v_all_1021_);
lean_dec_ref(v_params_1020_);
lean_dec(v_levels_1019_);
lean_dec_ref(v_toIndGroupInfo_1018_);
v_a_1059_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1028_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1028_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v_all_1021_);
lean_dec_ref(v_params_1020_);
lean_dec(v_levels_1019_);
lean_dec_ref(v_toIndGroupInfo_1018_);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2));
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
v___jp_1009_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; size_t v_sz_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1013_ = l_Array_toSubarray___redArg(v___y_1010_, v_lower_1011_, v_upper_1012_);
v___x_1014_ = l_Subarray_copy___redArg(v___x_1013_);
v_sz_1015_ = lean_array_size(v___x_1014_);
v___x_1016_ = ((size_t)0ULL);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_sz_1015_, v___x_1016_, v___x_1014_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___boxed(lean_object* v_igi_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_igi_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(lean_object* v_00_u03b1_1076_, lean_object* v_msg_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1084_, lean_object* v_msg_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(v_00_u03b1_1084_, v_msg_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
}
#ifdef __cplusplus
}
#endif
