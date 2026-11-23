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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInfo_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__0_value)}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst_default = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Structural_instInhabitedIndGroupInst = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedIndGroupInst_default___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0_value;
static const lean_array_object l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_91_, 2);
v___x_96_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_95_);
return v___x_96_;
}
else
{
lean_object* v_head_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_inc(v_tail_94_);
v_head_97_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_97_);
lean_dec_ref_known(v_x_91_, 2);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_dec(v_x_244_);
return v_x_245_;
}
else
{
lean_object* v_head_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_259_; 
v_head_247_ = lean_ctor_get(v_x_246_, 0);
v_tail_248_ = lean_ctor_get(v_x_246_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_259_ == 0)
{
v___x_250_ = v_x_246_;
v_isShared_251_ = v_isSharedCheck_259_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_head_247_);
lean_dec(v_x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_259_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
lean_inc(v_x_244_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 5);
lean_ctor_set(v___x_250_, 1, v_x_244_);
lean_ctor_set(v___x_250_, 0, v_x_245_);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_x_245_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_x_244_);
v___x_253_ = v_reuseFailAlloc_258_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Lean_instReprExpr_repr(v_head_247_, v___x_254_);
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_253_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v_x_245_ = v___x_256_;
v_x_246_ = v_tail_248_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_dec(v_x_260_);
return v_x_261_;
}
else
{
lean_object* v_head_263_; lean_object* v_tail_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_275_; 
v_head_263_ = lean_ctor_get(v_x_262_, 0);
v_tail_264_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_275_ == 0)
{
v___x_266_ = v_x_262_;
v_isShared_267_ = v_isSharedCheck_275_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_tail_264_);
lean_inc(v_head_263_);
lean_dec(v_x_262_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_275_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
lean_inc(v_x_260_);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 5);
lean_ctor_set(v___x_266_, 1, v_x_260_);
lean_ctor_set(v___x_266_, 0, v_x_261_);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_x_260_);
v___x_269_ = v_reuseFailAlloc_274_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Lean_instReprExpr_repr(v_head_263_, v___x_270_);
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_269_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(v_x_260_, v___x_272_, v_tail_264_);
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(lean_object* v___y_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Lean_instReprExpr_repr(v___y_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_281_; 
lean_dec(v_x_280_);
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_tail_282_; 
v_tail_282_ = lean_ctor_get(v_x_279_, 1);
if (lean_obj_tag(v_tail_282_) == 0)
{
lean_object* v_head_283_; lean_object* v___x_284_; 
lean_dec(v_x_280_);
v_head_283_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_head_283_);
lean_dec_ref_known(v_x_279_, 2);
v___x_284_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_283_);
return v___x_284_;
}
else
{
lean_object* v_head_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc(v_tail_282_);
v_head_285_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_head_285_);
lean_dec_ref_known(v_x_279_, 2);
v___x_286_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_285_);
v___x_287_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(v_x_280_, v___x_286_, v_tail_282_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(lean_object* v_xs_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_array_get_size(v_xs_288_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_nat_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_292_ = lean_array_to_list(v_xs_288_);
v___x_293_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_294_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(v___x_292_, v___x_293_);
v___x_295_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
v___x_296_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_294_);
v___x_298_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_295_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Std_Format_fill(v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v_xs_288_);
v___x_302_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10));
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_dec(v_x_303_);
return v_x_304_;
}
else
{
lean_object* v_head_306_; lean_object* v_tail_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_318_; 
v_head_306_ = lean_ctor_get(v_x_305_, 0);
v_tail_307_ = lean_ctor_get(v_x_305_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_318_ == 0)
{
v___x_309_ = v_x_305_;
v_isShared_310_ = v_isSharedCheck_318_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_tail_307_);
lean_inc(v_head_306_);
lean_dec(v_x_305_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_318_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
lean_inc(v_x_303_);
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 5);
lean_ctor_set(v___x_309_, 1, v_x_303_);
lean_ctor_set(v___x_309_, 0, v_x_304_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_304_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_x_303_);
v___x_312_ = v_reuseFailAlloc_317_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Lean_instReprLevel_repr(v_head_306_, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v_x_304_ = v___x_315_;
v_x_305_ = v_tail_307_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_dec(v_x_319_);
return v_x_320_;
}
else
{
lean_object* v_head_322_; lean_object* v_tail_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_334_; 
v_head_322_ = lean_ctor_get(v_x_321_, 0);
v_tail_323_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_325_ = v_x_321_;
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_tail_323_);
lean_inc(v_head_322_);
lean_dec(v_x_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
lean_inc(v_x_319_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 5);
lean_ctor_set(v___x_325_, 1, v_x_319_);
lean_ctor_set(v___x_325_, 0, v_x_320_);
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_x_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_x_319_);
v___x_328_ = v_reuseFailAlloc_333_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = l_Lean_instReprLevel_repr(v_head_322_, v___x_329_);
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_328_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(v_x_319_, v___x_331_, v_tail_323_);
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(lean_object* v___y_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = l_Lean_instReprLevel_repr(v___y_335_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_340_; 
lean_dec(v_x_339_);
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v_tail_341_; 
v_tail_341_ = lean_ctor_get(v_x_338_, 1);
if (lean_obj_tag(v_tail_341_) == 0)
{
lean_object* v_head_342_; lean_object* v___x_343_; 
lean_dec(v_x_339_);
v_head_342_ = lean_ctor_get(v_x_338_, 0);
lean_inc(v_head_342_);
lean_dec_ref_known(v_x_338_, 2);
v___x_343_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_342_);
return v___x_343_;
}
else
{
lean_object* v_head_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc(v_tail_341_);
v_head_344_ = lean_ctor_get(v_x_338_, 0);
lean_inc(v_head_344_);
lean_dec_ref_known(v_x_338_, 2);
v___x_345_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_344_);
v___x_346_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(v_x_339_, v___x_345_, v_tail_341_);
return v___x_346_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2));
v___x_352_ = lean_string_length(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3, &l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3);
v___x_354_ = lean_nat_to_int(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(lean_object* v_a_357_){
_start:
{
if (lean_obj_tag(v_a_357_) == 0)
{
lean_object* v___x_358_; 
v___x_358_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1));
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; 
v___x_359_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_360_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(v_a_357_, v___x_359_);
v___x_361_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4);
v___x_362_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5));
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_360_);
v___x_364_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_361_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = 0;
v___x_368_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*1, v___x_367_);
return v___x_368_;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(18u);
v___x_379_ = lean_nat_to_int(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(10u);
v___x_384_ = lean_nat_to_int(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(lean_object* v_x_388_){
_start:
{
lean_object* v_toIndGroupInfo_389_; lean_object* v_levels_390_; lean_object* v_params_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_toIndGroupInfo_389_ = lean_ctor_get(v_x_388_, 0);
lean_inc_ref(v_toIndGroupInfo_389_);
v_levels_390_ = lean_ctor_get(v_x_388_, 1);
lean_inc(v_levels_390_);
v_params_391_ = lean_ctor_get(v_x_388_, 2);
lean_inc_ref(v_params_391_);
lean_dec_ref(v_x_388_);
v___x_392_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5));
v___x_393_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3));
v___x_394_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4, &l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once, _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4);
v___x_395_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_toIndGroupInfo_389_);
v___x_396_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = 0;
v___x_398_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*1, v___x_397_);
v___x_399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_393_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2));
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_box(1);
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6));
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_392_);
v___x_407_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7, &l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once, _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7);
v___x_408_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(v_levels_390_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_397_);
v___x_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_406_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_400_);
v___x_413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_402_);
v___x_414_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9));
v___x_415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_392_);
v___x_417_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(v_params_391_);
v___x_418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_407_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*1, v___x_397_);
v___x_420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_416_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13);
v___x_422_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14));
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_420_);
v___x_424_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15));
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_421_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*1, v___x_397_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr(lean_object* v_x_428_, lean_object* v_prec_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed(lean_object* v_x_431_, lean_object* v_prec_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr(v_x_431_, v_prec_432_);
lean_dec(v_prec_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(lean_object* v_a_434_, lean_object* v_n_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(v_a_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___boxed(lean_object* v_a_437_, lean_object* v_n_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(v_a_437_, v_n_438_);
lean_dec(v_n_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object* v_igi_442_){
_start:
{
lean_object* v_toIndGroupInfo_443_; lean_object* v_levels_444_; lean_object* v_params_445_; lean_object* v_all_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_toIndGroupInfo_443_ = lean_ctor_get(v_igi_442_, 0);
lean_inc_ref(v_toIndGroupInfo_443_);
v_levels_444_ = lean_ctor_get(v_igi_442_, 1);
lean_inc(v_levels_444_);
v_params_445_ = lean_ctor_get(v_igi_442_, 2);
lean_inc_ref(v_params_445_);
lean_dec_ref(v_igi_442_);
v_all_446_ = lean_ctor_get(v_toIndGroupInfo_443_, 0);
lean_inc_ref(v_all_446_);
lean_dec_ref(v_toIndGroupInfo_443_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get(v___x_447_, v_all_446_, v___x_448_);
lean_dec_ref(v_all_446_);
v___x_450_ = l_Lean_Expr_const___override(v___x_449_, v_levels_444_);
v___x_451_ = l_Lean_mkAppN(v___x_450_, v_params_445_);
lean_dec_ref(v_params_445_);
v___x_452_ = l_Lean_MessageData_ofExpr(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(lean_object* v_fst_455_, lean_object* v_snd_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_fst_455_);
lean_ctor_set(v___x_457_, 1, v_snd_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(uint8_t v___x_458_, uint8_t v_____do__lift_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
if (v_____do__lift_459_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_box(v___x_458_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
else
{
uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = 0;
v___x_468_ = lean_box(v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1___boxed(lean_object* v___x_470_, lean_object* v_____do__lift_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_1798__boxed_477_; uint8_t v_____do__lift_1799__boxed_478_; lean_object* v_res_479_; 
v___x_1798__boxed_477_ = lean_unbox(v___x_470_);
v_____do__lift_1799__boxed_478_ = lean_unbox(v_____do__lift_471_);
v_res_479_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(v___x_1798__boxed_477_, v_____do__lift_1799__boxed_478_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_479_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
uint8_t v___x_481_; 
v___x_481_ = 1;
return v___x_481_;
}
else
{
lean_object* v_head_482_; lean_object* v_tail_483_; lean_object* v_fst_484_; lean_object* v_snd_485_; uint8_t v___x_486_; 
v_head_482_ = lean_ctor_get(v_x_480_, 0);
v_tail_483_ = lean_ctor_get(v_x_480_, 1);
v_fst_484_ = lean_ctor_get(v_head_482_, 0);
v_snd_485_ = lean_ctor_get(v_head_482_, 1);
v___x_486_ = l_Lean_Level_isEquiv(v_fst_484_, v_snd_485_);
if (v___x_486_ == 0)
{
return v___x_486_;
}
else
{
v_x_480_ = v_tail_483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v_x_488_);
lean_dec(v_x_488_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v_as_493_, size_t v_i_494_, size_t v_stop_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_eq(v_i_494_, v_stop_495_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; uint8_t v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; 
v___x_506_ = lean_array_uget_borrowed(v_as_493_, v_i_494_);
v_fst_507_ = lean_ctor_get(v___x_506_, 0);
v_snd_508_ = lean_ctor_get(v___x_506_, 1);
v___x_509_ = lean_nat_dec_eq(v___x_491_, v___x_492_);
v___x_510_ = 1;
lean_inc(v_snd_508_);
lean_inc(v_fst_507_);
v___x_511_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_507_, v_snd_508_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_521_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_unbox(v_a_512_);
lean_dec(v_a_512_);
if (v___x_516_ == 0)
{
if (v___x_509_ == 0)
{
lean_del_object(v___x_514_);
goto v___jp_501_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_box(v___x_510_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_del_object(v___x_514_);
goto v___jp_501_;
}
}
}
else
{
return v___x_511_;
}
}
else
{
uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = 0;
v___x_523_ = lean_box(v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
v___jp_501_:
{
size_t v___x_502_; size_t v___x_503_; 
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_494_, v___x_502_);
v_i_494_ = v___x_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1___boxed(lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_as_527_, lean_object* v_i_528_, lean_object* v_stop_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_529_);
lean_dec(v_stop_529_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_525_, v___x_526_, v_as_527_, v_i_boxed_535_, v_stop_boxed_536_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_as_527_);
lean_dec(v___x_526_);
lean_dec(v___x_525_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object* v_igi1_541_, lean_object* v_igi2_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_toIndGroupInfo_548_; lean_object* v_levels_549_; lean_object* v_params_550_; lean_object* v_toIndGroupInfo_551_; lean_object* v_levels_552_; lean_object* v_params_553_; uint8_t v___x_554_; 
v_toIndGroupInfo_548_ = lean_ctor_get(v_igi1_541_, 0);
lean_inc_ref(v_toIndGroupInfo_548_);
v_levels_549_ = lean_ctor_get(v_igi1_541_, 1);
lean_inc(v_levels_549_);
v_params_550_ = lean_ctor_get(v_igi1_541_, 2);
lean_inc_ref(v_params_550_);
lean_dec_ref(v_igi1_541_);
v_toIndGroupInfo_551_ = lean_ctor_get(v_igi2_542_, 0);
lean_inc_ref(v_toIndGroupInfo_551_);
v_levels_552_ = lean_ctor_get(v_igi2_542_, 1);
lean_inc(v_levels_552_);
v_params_553_ = lean_ctor_get(v_igi2_542_, 2);
lean_inc_ref(v_params_553_);
lean_dec_ref(v_igi2_542_);
v___x_554_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_toIndGroupInfo_548_, v_toIndGroupInfo_551_);
lean_dec_ref(v_toIndGroupInfo_551_);
lean_dec_ref(v_toIndGroupInfo_548_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_params_553_);
lean_dec(v_levels_552_);
lean_dec_ref(v_params_550_);
lean_dec(v_levels_549_);
v___x_555_ = lean_box(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = l_List_lengthTR___redArg(v_levels_549_);
v___x_558_ = l_List_lengthTR___redArg(v_levels_552_);
v___x_559_ = lean_nat_dec_eq(v___x_557_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_557_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v_params_553_);
lean_dec(v_levels_552_);
lean_dec_ref(v_params_550_);
lean_dec(v_levels_549_);
v___x_560_ = lean_box(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v___f_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___f_562_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__0));
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_isDefEq___closed__1));
v___x_565_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_562_, v_levels_549_, v_levels_552_, v___x_564_);
v___x_566_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v___x_565_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v_params_553_);
lean_dec_ref(v_params_550_);
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___y_573_; 
v___x_569_ = lean_array_get_size(v_params_550_);
v___x_570_ = lean_array_get_size(v_params_553_);
v___x_571_ = lean_nat_dec_eq(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec_ref(v_params_553_);
lean_dec_ref(v_params_550_);
v___x_585_ = lean_box(v___x_571_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = l_Array_zip___redArg(v_params_550_, v_params_553_);
lean_dec_ref(v_params_553_);
lean_dec_ref(v_params_550_);
v___x_588_ = lean_array_get_size(v___x_587_);
v___x_589_ = lean_nat_dec_lt(v___x_563_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v___x_587_);
v___x_590_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(v___x_571_, v___x_589_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
v___y_573_ = v___x_590_;
goto v___jp_572_;
}
else
{
if (v___x_589_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec_ref(v___x_587_);
v___x_591_ = lean_box(v___x_571_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_588_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_569_, v___x_570_, v___x_587_, v___x_593_, v___x_594_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec_ref(v___x_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; uint8_t v___x_597_; lean_object* v___x_598_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
v___x_598_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__1(v___x_571_, v___x_597_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
v___y_573_ = v___x_598_;
goto v___jp_572_;
}
else
{
return v___x_595_;
}
}
}
}
v___jp_572_:
{
lean_object* v_a_574_; uint8_t v___x_575_; 
v_a_574_ = lean_ctor_get(v___y_573_, 0);
v___x_575_ = lean_unbox(v_a_574_);
if (v___x_575_ == 0)
{
return v___y_573_;
}
else
{
lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
v_isSharedCheck_583_ = !lean_is_exclusive(v___y_573_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v___y_573_, 0);
lean_dec(v_unused_584_);
v___x_577_ = v___y_573_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_dec(v___y_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_box(v___x_571_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(lean_object* v_igi1_599_, lean_object* v_igi2_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_igi1_599_, v_igi2_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn(lean_object* v_group_607_, lean_object* v_lvl_608_, lean_object* v_idx_609_){
_start:
{
lean_object* v_toIndGroupInfo_610_; lean_object* v_levels_611_; lean_object* v_params_612_; lean_object* v_n_613_; lean_object* v_us_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_toIndGroupInfo_610_ = lean_ctor_get(v_group_607_, 0);
v_levels_611_ = lean_ctor_get(v_group_607_, 1);
v_params_612_ = lean_ctor_get(v_group_607_, 2);
v_n_613_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_610_, v_idx_609_);
lean_inc(v_levels_611_);
v_us_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_614_, 0, v_lvl_608_);
lean_ctor_set(v_us_614_, 1, v_levels_611_);
v___x_615_ = l_Lean_Expr_const___override(v_n_613_, v_us_614_);
v___x_616_ = l_Lean_mkAppN(v___x_615_, v_params_612_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(lean_object* v_group_617_, lean_object* v_lvl_618_, lean_object* v_idx_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Elab_Structural_IndGroupInst_brecOn(v_group_617_, v_lvl_618_, v_idx_619_);
lean_dec(v_idx_619_);
lean_dec_ref(v_group_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___f_628_; lean_object* v___x_893__overap_629_; lean_object* v___x_630_; 
v___f_628_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0));
v___x_893__overap_629_ = lean_panic_fn_borrowed(v___f_628_, v_msg_622_);
lean_inc(v___y_626_);
lean_inc_ref(v___y_625_);
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
v___x_630_ = lean_apply_5(v___x_893__overap_629_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, lean_box(0));
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___boxed(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(lean_object* v_k_638_, lean_object* v_b_639_, lean_object* v_c_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_646_ = lean_apply_7(v_k_638_, v_b_639_, v_c_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed(lean_object* v_k_647_, lean_object* v_b_648_, lean_object* v_c_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(v_k_647_, v_b_648_, v_c_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(lean_object* v_type_656_, lean_object* v_k_657_, uint8_t v_cleanupAnnotations_658_, uint8_t v_whnfType_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_665_, 0, v_k_657_);
v___x_666_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_656_, v___f_665_, v_cleanupAnnotations_658_, v_whnfType_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_666_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_666_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___boxed(lean_object* v_type_683_, lean_object* v_k_684_, lean_object* v_cleanupAnnotations_685_, lean_object* v_whnfType_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_692_; uint8_t v_whnfType_boxed_693_; lean_object* v_res_694_; 
v_cleanupAnnotations_boxed_692_ = lean_unbox(v_cleanupAnnotations_685_);
v_whnfType_boxed_693_ = lean_unbox(v_whnfType_686_);
v_res_694_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_683_, v_k_684_, v_cleanupAnnotations_boxed_692_, v_whnfType_boxed_693_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(lean_object* v_00_u03b1_695_, lean_object* v_type_696_, lean_object* v_k_697_, uint8_t v_cleanupAnnotations_698_, uint8_t v_whnfType_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_696_, v_k_697_, v_cleanupAnnotations_698_, v_whnfType_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___boxed(lean_object* v_00_u03b1_706_, lean_object* v_type_707_, lean_object* v_k_708_, lean_object* v_cleanupAnnotations_709_, lean_object* v_whnfType_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_716_; uint8_t v_whnfType_boxed_717_; lean_object* v_res_718_; 
v_cleanupAnnotations_boxed_716_ = lean_unbox(v_cleanupAnnotations_709_);
v_whnfType_boxed_717_ = lean_unbox(v_whnfType_710_);
v_res_718_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(v_00_u03b1_706_, v_type_707_, v_k_708_, v_cleanupAnnotations_boxed_716_, v_whnfType_boxed_717_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___f_725_; lean_object* v___x_1971__overap_726_; lean_object* v___x_727_; 
v___f_725_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0));
v___x_1971__overap_726_ = lean_panic_fn_borrowed(v___f_725_, v_msg_719_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_727_ = lean_apply_5(v___x_1971__overap_726_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, lean_box(0));
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4___boxed(lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v_msg_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2));
v___x_739_ = lean_unsigned_to_nat(6u);
v___x_740_ = lean_unsigned_to_nat(113u);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1));
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0));
v___x_743_ = l_mkPanicMessageWithDecl(v___x_742_, v___x_741_, v___x_740_, v___x_739_, v___x_738_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(lean_object* v___x_744_, lean_object* v___x_745_, uint8_t v___x_746_, lean_object* v_xs_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_array_get_size(v_xs_747_);
v___x_755_ = lean_nat_dec_lt(v___x_744_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref(v_xs_747_);
v___x_756_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3);
v___x_757_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v___x_756_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_sub(v___x_754_, v___x_758_);
v___x_760_ = lean_array_get_borrowed(v___x_745_, v_xs_747_, v___x_759_);
lean_dec(v___x_759_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___x_760_);
v___x_761_ = lean_infer_type(v___x_760_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = lean_array_pop(v_xs_747_);
v___x_764_ = 1;
v___x_765_ = l_Lean_Meta_mkForallFVars(v___x_763_, v_a_762_, v___x_746_, v___x_755_, v___x_755_, v___x_764_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v___x_763_);
return v___x_765_;
}
else
{
lean_dec_ref(v_xs_747_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_xs_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___x_3354__boxed_776_; lean_object* v_res_777_; 
v___x_3354__boxed_776_ = lean_unbox(v___x_768_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(v___x_766_, v___x_767_, v___x_3354__boxed_776_, v_xs_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v_x_770_);
lean_dec_ref(v___x_767_);
lean_dec(v___x_766_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(lean_object* v___x_778_, size_t v_sz_779_, size_t v_i_780_, lean_object* v_bs_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_780_, v_sz_779_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_bs_781_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v_v_794_; lean_object* v_bs_x27_795_; lean_object* v___x_796_; 
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = l_Lean_instInhabitedExpr;
v___x_791_ = lean_nat_dec_eq(v___x_778_, v___x_789_);
v___x_792_ = lean_box(v___x_791_);
v___f_793_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed), 10, 3);
lean_closure_set(v___f_793_, 0, v___x_789_);
lean_closure_set(v___f_793_, 1, v___x_790_);
lean_closure_set(v___f_793_, 2, v___x_792_);
v_v_794_ = lean_array_uget(v_bs_781_, v_i_780_);
v_bs_x27_795_ = lean_array_uset(v_bs_781_, v_i_780_, v___x_789_);
v___x_796_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_v_794_, v___f_793_, v___x_791_, v___x_791_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_780_, v___x_798_);
v___x_800_ = lean_array_uset(v_bs_x27_795_, v_i_780_, v_a_797_);
v_i_780_ = v___x_799_;
v_bs_781_ = v___x_800_;
goto _start;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_bs_x27_795_);
v_a_802_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_796_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_796_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___boxed(lean_object* v___x_810_, lean_object* v_sz_811_, lean_object* v_i_812_, lean_object* v_bs_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v_sz_boxed_819_ = lean_unbox_usize(v_sz_811_);
lean_dec(v_sz_811_);
v_i_boxed_820_ = lean_unbox_usize(v_i_812_);
lean_dec(v_i_812_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v___x_810_, v_sz_boxed_819_, v_i_boxed_820_, v_bs_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___x_810_);
return v_res_821_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_instMonadEIO___redArg();
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(lean_object* v_msg_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_toApplicative_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_896_; 
v___x_833_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0);
v___x_834_ = l_StateRefT_x27_instMonad___redArg(v___x_833_);
v_toApplicative_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_834_, 1);
lean_dec(v_unused_897_);
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_896_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_toApplicative_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_896_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v_toFunctor_839_; lean_object* v_toSeq_840_; lean_object* v_toSeqLeft_841_; lean_object* v_toSeqRight_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_894_; 
v_toFunctor_839_ = lean_ctor_get(v_toApplicative_835_, 0);
v_toSeq_840_ = lean_ctor_get(v_toApplicative_835_, 2);
v_toSeqLeft_841_ = lean_ctor_get(v_toApplicative_835_, 3);
v_toSeqRight_842_ = lean_ctor_get(v_toApplicative_835_, 4);
v_isSharedCheck_894_ = !lean_is_exclusive(v_toApplicative_835_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_toApplicative_835_, 1);
lean_dec(v_unused_895_);
v___x_844_ = v_toApplicative_835_;
v_isShared_845_ = v_isSharedCheck_894_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_toSeqRight_842_);
lean_inc(v_toSeqLeft_841_);
lean_inc(v_toSeq_840_);
lean_inc(v_toFunctor_839_);
lean_dec(v_toApplicative_835_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_894_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___f_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_855_; 
v___f_846_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1));
v___f_847_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_839_);
v___f_848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_848_, 0, v_toFunctor_839_);
v___f_849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_849_, 0, v_toFunctor_839_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___f_848_);
lean_ctor_set(v___x_850_, 1, v___f_849_);
v___f_851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_851_, 0, v_toSeqRight_842_);
v___f_852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_852_, 0, v_toSeqLeft_841_);
v___f_853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_853_, 0, v_toSeq_840_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v___f_851_);
lean_ctor_set(v___x_844_, 3, v___f_852_);
lean_ctor_set(v___x_844_, 2, v___f_853_);
lean_ctor_set(v___x_844_, 1, v___f_846_);
lean_ctor_set(v___x_844_, 0, v___x_850_);
v___x_855_ = v___x_844_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___f_846_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v___f_853_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v___f_852_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v___f_851_);
v___x_855_ = v_reuseFailAlloc_893_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___f_847_);
lean_ctor_set(v___x_837_, 0, v___x_855_);
v___x_857_ = v___x_837_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___f_847_);
v___x_857_ = v_reuseFailAlloc_892_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v_toApplicative_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_890_; 
v___x_858_ = l_StateRefT_x27_instMonad___redArg(v___x_857_);
v_toApplicative_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_858_, 1);
lean_dec(v_unused_891_);
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_890_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_toApplicative_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_890_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_toFunctor_863_; lean_object* v_toSeq_864_; lean_object* v_toSeqLeft_865_; lean_object* v_toSeqRight_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_888_; 
v_toFunctor_863_ = lean_ctor_get(v_toApplicative_859_, 0);
v_toSeq_864_ = lean_ctor_get(v_toApplicative_859_, 2);
v_toSeqLeft_865_ = lean_ctor_get(v_toApplicative_859_, 3);
v_toSeqRight_866_ = lean_ctor_get(v_toApplicative_859_, 4);
v_isSharedCheck_888_ = !lean_is_exclusive(v_toApplicative_859_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_toApplicative_859_, 1);
lean_dec(v_unused_889_);
v___x_868_ = v_toApplicative_859_;
v_isShared_869_ = v_isSharedCheck_888_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_toSeqRight_866_);
lean_inc(v_toSeqLeft_865_);
lean_inc(v_toSeq_864_);
lean_inc(v_toFunctor_863_);
lean_dec(v_toApplicative_859_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_888_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_879_; 
v___f_870_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3));
v___f_871_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_863_);
v___f_872_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_872_, 0, v_toFunctor_863_);
v___f_873_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_873_, 0, v_toFunctor_863_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___f_872_);
lean_ctor_set(v___x_874_, 1, v___f_873_);
v___f_875_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_875_, 0, v_toSeqRight_866_);
v___f_876_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_876_, 0, v_toSeqLeft_865_);
v___f_877_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_877_, 0, v_toSeq_864_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 4, v___f_875_);
lean_ctor_set(v___x_868_, 3, v___f_876_);
lean_ctor_set(v___x_868_, 2, v___f_877_);
lean_ctor_set(v___x_868_, 1, v___f_870_);
lean_ctor_set(v___x_868_, 0, v___x_874_);
v___x_879_ = v___x_868_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___f_870_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___f_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___f_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v___f_875_);
v___x_879_ = v_reuseFailAlloc_887_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___f_871_);
lean_ctor_set(v___x_861_, 0, v___x_879_);
v___x_881_ = v___x_861_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___f_871_);
v___x_881_ = v_reuseFailAlloc_886_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_2577__overap_884_; lean_object* v___x_885_; 
v___x_882_ = lean_box(0);
v___x_883_ = l_instInhabitedOfMonad___redArg(v___x_881_, v___x_882_);
v___x_2577__overap_884_ = lean_panic_fn_borrowed(v___x_883_, v_msg_827_);
lean_dec(v___x_883_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
v___x_885_ = lean_apply_5(v___x_2577__overap_884_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, lean_box(0));
return v___x_885_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___boxed(lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(lean_object* v_msgData_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_env_912_; uint8_t v___x_913_; lean_object* v_env_914_; lean_object* v___x_915_; lean_object* v_toCold_916_; lean_object* v_mctx_917_; lean_object* v_lctx_918_; lean_object* v_options_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_911_ = lean_st_ref_get(v___y_909_);
v_env_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref(v_env_912_);
lean_dec(v___x_911_);
v___x_913_ = 0;
v_env_914_ = l_Lean_Environment_setRecordingDeps(v_env_912_, v___x_913_);
v___x_915_ = lean_st_ref_get(v___y_907_);
v_toCold_916_ = lean_ctor_get(v___y_908_, 0);
v_mctx_917_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_mctx_917_);
lean_dec(v___x_915_);
v_lctx_918_ = lean_ctor_get(v___y_906_, 2);
v_options_919_ = lean_ctor_get(v_toCold_916_, 2);
lean_inc_ref(v_options_919_);
lean_inc_ref(v_lctx_918_);
v___x_920_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_920_, 0, v_env_914_);
lean_ctor_set(v___x_920_, 1, v_mctx_917_);
lean_ctor_set(v___x_920_, 2, v_lctx_918_);
lean_ctor_set(v___x_920_, 3, v_options_919_);
v___x_921_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v_msgData_905_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msgData_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(lean_object* v_msg_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_ref_936_; lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v_ref_936_ = lean_ctor_get(v___y_933_, 2);
v___x_937_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msg_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_946_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
lean_inc(v_ref_936_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_ref_936_);
lean_ctor_set(v___x_942_, 1, v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg___boxed(lean_object* v_msg_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_953_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_963_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6));
v___x_964_ = lean_unsigned_to_nat(11u);
v___x_965_ = lean_unsigned_to_nat(129u);
v___x_966_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5));
v___x_967_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4));
v___x_968_ = l_mkPanicMessageWithDecl(v___x_967_, v___x_966_, v___x_965_, v___x_964_, v___x_963_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(lean_object* v_constName_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_983_; lean_object* v_env_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v___x_983_ = lean_st_ref_get(v___y_973_);
v_env_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc_ref(v_env_984_);
lean_dec(v___x_983_);
v___x_985_ = 0;
lean_inc(v_constName_969_);
v___x_986_ = l_Lean_Environment_findAsync_x3f(v_env_984_, v_constName_969_, v___x_985_);
if (lean_obj_tag(v___x_986_) == 1)
{
lean_object* v_val_987_; uint8_t v_kind_988_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_986_, 1);
v_kind_988_ = lean_ctor_get_uint8(v_val_987_, sizeof(void*)*3);
if (v_kind_988_ == 7)
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_987_);
if (lean_obj_tag(v___x_989_) == 7)
{
lean_object* v_val_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_constName_969_);
v_val_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_val_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_val_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref(v___x_989_);
v___x_998_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7);
v___x_999_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v___x_998_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
if (lean_obj_tag(v_a_1000_) == 0)
{
lean_del_object(v___x_1002_);
goto v___jp_975_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
lean_dec(v_constName_969_);
v_val_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_a_1000_, 1);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_val_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_val_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_constName_969_);
v_a_1009_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_999_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_999_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
else
{
lean_dec(v_val_987_);
goto v___jp_975_;
}
}
else
{
lean_dec(v___x_986_);
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_976_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1);
v___x_977_ = 0;
v___x_978_ = l_Lean_MessageData_ofConstName(v_constName_969_, v___x_977_);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_976_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v___x_981_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___boxed(lean_object* v_constName_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_constName_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0));
v___x_1026_ = lean_unsigned_to_nat(2u);
v___x_1027_ = lean_unsigned_to_nat(104u);
v___x_1028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1));
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0));
v___x_1030_ = l_mkPanicMessageWithDecl(v___x_1029_, v___x_1028_, v___x_1027_, v___x_1026_, v___x_1025_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object* v_igi_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_toIndGroupInfo_1039_; lean_object* v_levels_1040_; lean_object* v_params_1041_; lean_object* v_all_1042_; lean_object* v_numNested_1043_; lean_object* v___y_1045_; lean_object* v_lower_1046_; lean_object* v_upper_1047_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_toIndGroupInfo_1039_ = lean_ctor_get(v_igi_1033_, 0);
lean_inc_ref(v_toIndGroupInfo_1039_);
v_levels_1040_ = lean_ctor_get(v_igi_1033_, 1);
lean_inc(v_levels_1040_);
v_params_1041_ = lean_ctor_get(v_igi_1033_, 2);
lean_inc_ref(v_params_1041_);
lean_dec_ref(v_igi_1033_);
v_all_1042_ = lean_ctor_get(v_toIndGroupInfo_1039_, 0);
lean_inc_ref(v_all_1042_);
v_numNested_1043_ = lean_ctor_get(v_toIndGroupInfo_1039_, 1);
lean_inc(v_numNested_1043_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_nat_dec_eq(v_numNested_1043_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_recName_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_array_get_borrowed(v___x_1055_, v_all_1042_, v___x_1053_);
lean_inc(v___x_1056_);
v_recName_1057_ = l_Lean_mkRecName(v___x_1056_);
lean_inc(v_recName_1057_);
v___x_1058_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_recName_1057_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v_toConstantVal_1060_; lean_object* v_numMotives_1061_; lean_object* v___y_1063_; lean_object* v___x_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1086_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v_toConstantVal_1060_ = lean_ctor_get(v_a_1059_, 0);
lean_inc_ref(v_toConstantVal_1060_);
v_numMotives_1061_ = lean_ctor_get(v_a_1059_, 4);
lean_inc(v_numMotives_1061_);
lean_dec(v_a_1059_);
v___x_1071_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_1039_);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_toIndGroupInfo_1039_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; 
v_unused_1087_ = lean_ctor_get(v_toIndGroupInfo_1039_, 1);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_toIndGroupInfo_1039_, 0);
lean_dec(v_unused_1088_);
v___x_1073_ = v_toIndGroupInfo_1039_;
v_isShared_1074_ = v_isSharedCheck_1086_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v_toIndGroupInfo_1039_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1086_;
goto v_resetjp_1072_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = l_Lean_Expr_const___override(v_recName_1057_, v___y_1063_);
v___x_1065_ = l_Lean_mkAppN(v___x_1064_, v_params_1041_);
lean_dec_ref(v_params_1041_);
v___x_1066_ = l_Lean_Meta_inferArgumentTypesN(v_numMotives_1061_, v___x_1065_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = lean_array_get_size(v_all_1042_);
lean_dec_ref(v_all_1042_);
v___x_1069_ = lean_array_get_size(v_a_1067_);
v___x_1070_ = lean_nat_dec_le(v___x_1068_, v___x_1053_);
if (v___x_1070_ == 0)
{
v___y_1045_ = v_a_1067_;
v_lower_1046_ = v___x_1068_;
v_upper_1047_ = v___x_1069_;
goto v___jp_1044_;
}
else
{
v___y_1045_ = v_a_1067_;
v_lower_1046_ = v___x_1053_;
v_upper_1047_ = v___x_1069_;
goto v___jp_1044_;
}
}
else
{
lean_dec(v_numNested_1043_);
lean_dec_ref(v_all_1042_);
return v___x_1066_;
}
}
v_resetjp_1072_:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_nat_dec_eq(v_numMotives_1061_, v___x_1071_);
lean_dec(v___x_1071_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_del_object(v___x_1073_);
lean_dec(v_numMotives_1061_);
lean_dec_ref(v_toConstantVal_1060_);
lean_dec(v_recName_1057_);
lean_dec(v_numNested_1043_);
lean_dec_ref(v_all_1042_);
lean_dec_ref(v_params_1041_);
lean_dec(v_levels_1040_);
v___x_1076_ = lean_obj_once(&l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1, &l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once, _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1);
v___x_1077_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v___x_1076_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1077_;
}
else
{
lean_object* v_levelParams_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_levelParams_1078_ = lean_ctor_get(v_toConstantVal_1060_, 1);
lean_inc(v_levelParams_1078_);
lean_dec_ref(v_toConstantVal_1060_);
v___x_1079_ = l_List_lengthTR___redArg(v_levels_1040_);
v___x_1080_ = l_List_lengthTR___redArg(v_levelParams_1078_);
lean_dec(v_levelParams_1078_);
v___x_1081_ = lean_nat_dec_eq(v___x_1079_, v___x_1080_);
lean_dec(v___x_1080_);
lean_dec(v___x_1079_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 1, v_levels_1040_);
lean_ctor_set(v___x_1073_, 0, v___x_1082_);
v___x_1084_ = v___x_1073_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_levels_1040_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v___y_1063_ = v___x_1084_;
goto v___jp_1062_;
}
}
else
{
lean_del_object(v___x_1073_);
v___y_1063_ = v_levels_1040_;
goto v___jp_1062_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_recName_1057_);
lean_dec(v_numNested_1043_);
lean_dec_ref(v_all_1042_);
lean_dec_ref(v_params_1041_);
lean_dec(v_levels_1040_);
lean_dec_ref(v_toIndGroupInfo_1039_);
v_a_1089_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1058_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1058_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_numNested_1043_);
lean_dec_ref(v_all_1042_);
lean_dec_ref(v_params_1041_);
lean_dec(v_levels_1040_);
lean_dec_ref(v_toIndGroupInfo_1039_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2));
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
v___jp_1044_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; size_t v_sz_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = l_Array_toSubarray___redArg(v___y_1045_, v_lower_1046_, v_upper_1047_);
v___x_1049_ = l_Subarray_copy___redArg(v___x_1048_);
v_sz_1050_ = lean_array_size(v___x_1049_);
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_numNested_1043_, v_sz_1050_, v___x_1051_, v___x_1049_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_numNested_1043_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___boxed(lean_object* v_igi_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_igi_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(lean_object* v_00_u03b1_1106_, lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_msg_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(v_00_u03b1_1114_, v_msg_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
