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
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
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
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1_ = stack[0].m_obj;
lean_object* v_ys_2_ = stack[1].m_obj;
lean_object* v_x_3_ = stack[2].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_xs_1_, v_ys_2_, v_x_3_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg___boxed(lean_object* v_xs_13_, lean_object* v_ys_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_xs_13_, v_ys_14_, v_x_15_);
lean_dec_ref(v_ys_14_);
lean_dec_ref(v_xs_13_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_all_20_; lean_object* v_numNested_21_; lean_object* v_all_22_; lean_object* v_numNested_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_all_20_ = lean_ctor_get(v_x_18_, 0);
v_numNested_21_ = lean_ctor_get(v_x_18_, 1);
v_all_22_ = lean_ctor_get(v_x_19_, 0);
v_numNested_23_ = lean_ctor_get(v_x_19_, 1);
v___x_24_ = lean_array_get_size(v_all_20_);
v___x_25_ = lean_array_get_size(v_all_22_);
v___x_26_ = lean_nat_dec_eq(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_all_20_, v_all_22_, v___x_24_);
if (v___x_27_ == 0)
{
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_eq(v_numNested_21_, v_numNested_23_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_instBEqIndGroupInfo_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_18_ = stack[0].m_obj;
lean_object* v_x_19_ = stack[1].m_obj;
uint8_t v_res_29_;
v_res_29_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_x_18_, v_x_19_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instBEqIndGroupInfo_beq___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_x_30_, v_x_31_);
lean_dec_ref(v_x_31_);
lean_dec_ref(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(lean_object* v_xs_34_, lean_object* v_ys_35_, lean_object* v_hsz_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___redArg(v_xs_34_, v_ys_35_, v_x_37_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_34_ = stack[0].m_obj;
lean_object* v_ys_35_ = stack[1].m_obj;
lean_object* v_x_37_ = stack[3].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(v_xs_34_, v_ys_35_, lean_box(0), v_x_37_, lean_box(0));
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0___boxed(lean_object* v_xs_41_, lean_object* v_ys_42_, lean_object* v_hsz_43_, lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_instBEqIndGroupInfo_beq_spec__0(v_xs_41_, v_ys_42_, v_hsz_43_, v_x_44_, v_x_45_);
lean_dec_ref(v_ys_42_);
lean_dec_ref(v_xs_41_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__1(lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_nat_to_int(v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_Lean_Name_reprPrec(v___y_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_dec(v_x_62_);
return v_x_63_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_77_; 
v_head_65_ = lean_ctor_get(v_x_64_, 0);
v_tail_66_ = lean_ctor_get(v_x_64_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_x_64_);
if (v_isSharedCheck_77_ == 0)
{
v___x_68_ = v_x_64_;
v_isShared_69_ = v_isSharedCheck_77_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_tail_66_);
lean_inc(v_head_65_);
lean_dec(v_x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_77_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
lean_inc(v_x_62_);
if (v_isShared_69_ == 0)
{
lean_ctor_set_tag(v___x_68_, 5);
lean_ctor_set(v___x_68_, 1, v_x_62_);
lean_ctor_set(v___x_68_, 0, v_x_63_);
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_x_63_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_x_62_);
v___x_71_ = v_reuseFailAlloc_76_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = l_Lean_Name_reprPrec(v_head_65_, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_71_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v_x_63_ = v___x_74_;
v_x_64_ = v_tail_66_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_dec(v_x_78_);
return v_x_79_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_93_; 
v_head_81_ = lean_ctor_get(v_x_80_, 0);
v_tail_82_ = lean_ctor_get(v_x_80_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_93_ == 0)
{
v___x_84_ = v_x_80_;
v_isShared_85_ = v_isSharedCheck_93_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_head_81_);
lean_dec(v_x_80_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_93_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
lean_inc(v_x_78_);
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 5);
lean_ctor_set(v___x_84_, 1, v_x_78_);
lean_ctor_set(v___x_84_, 0, v_x_79_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_x_79_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_x_78_);
v___x_87_ = v_reuseFailAlloc_92_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = l_Lean_Name_reprPrec(v_head_81_, v___x_88_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_87_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2_spec__3(v_x_78_, v___x_90_, v_tail_82_);
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_x_95_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v_tail_97_; 
v_tail_97_ = lean_ctor_get(v_x_94_, 1);
if (lean_obj_tag(v_tail_97_) == 0)
{
lean_object* v_head_98_; lean_object* v___x_99_; 
lean_dec(v_x_95_);
v_head_98_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_head_98_);
lean_dec_ref_known(v_x_94_, 2);
v___x_99_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_98_);
return v___x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc(v_tail_97_);
v_head_100_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_head_100_);
lean_dec_ref_known(v_x_94_, 2);
v___x_101_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0___lam__0(v_head_100_);
v___x_102_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0_spec__2(v_x_95_, v___x_101_, v_tail_97_);
return v___x_102_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__0));
v___x_112_ = lean_string_length(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__5);
v___x_114_ = lean_nat_to_int(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(lean_object* v_xs_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_array_get_size(v_xs_122_);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_dec_eq(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_126_ = lean_array_to_list(v_xs_122_);
v___x_127_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_128_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0_spec__0(v___x_126_, v___x_127_);
v___x_129_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
v___x_130_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_128_);
v___x_132_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_129_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = l_Std_Format_fill(v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
lean_dec_ref(v_xs_122_);
v___x_136_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10));
return v___x_136_;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(7u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(13u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__0));
v___x_159_ = lean_string_length(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__12);
v___x_161_ = lean_nat_to_int(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(lean_object* v_x_166_){
_start:
{
lean_object* v_all_167_; lean_object* v_numNested_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_202_; 
v_all_167_ = lean_ctor_get(v_x_166_, 0);
v_numNested_168_ = lean_ctor_get(v_x_166_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_202_ == 0)
{
v___x_170_ = v_x_166_;
v_isShared_171_ = v_isSharedCheck_202_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_numNested_168_);
lean_inc(v_all_167_);
lean_dec(v_x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_202_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5));
v___x_173_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__6));
v___x_174_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__7);
v___x_175_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0(v_all_167_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 4);
lean_ctor_set(v___x_170_, 1, v___x_175_);
lean_ctor_set(v___x_170_, 0, v___x_174_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_201_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_178_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_173_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_box(1);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__9));
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_172_);
v___x_188_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__10);
v___x_189_ = l_Nat_reprFast(v_numNested_168_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_188_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_178_);
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_187_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13);
v___x_195_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14));
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_193_);
v___x_197_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_194_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_178_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr(lean_object* v_x_203_, lean_object* v_prec_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInfo_repr___boxed(lean_object* v_x_206_, lean_object* v_prec_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr(v_x_206_, v_prec_207_);
lean_dec(v_prec_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object* v_indInfo_211_){
_start:
{
lean_object* v_all_212_; lean_object* v_numNested_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_all_212_ = lean_ctor_get(v_indInfo_211_, 3);
lean_inc(v_all_212_);
v_numNested_213_ = lean_ctor_get(v_indInfo_211_, 5);
lean_inc(v_numNested_213_);
lean_dec_ref(v_indInfo_211_);
v___x_214_ = lean_array_mk(v_all_212_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_numNested_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object* v_group_216_){
_start:
{
lean_object* v_all_217_; lean_object* v_numNested_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_all_217_ = lean_ctor_get(v_group_216_, 0);
v_numNested_218_ = lean_ctor_get(v_group_216_, 1);
v___x_219_ = lean_array_get_size(v_all_217_);
v___x_220_ = lean_nat_add(v___x_219_, v_numNested_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives___boxed(lean_object* v_group_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_group_221_);
lean_dec_ref(v_group_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object* v_info_223_, lean_object* v_idx_224_){
_start:
{
lean_object* v_all_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_all_225_ = lean_ctor_get(v_info_223_, 0);
v___x_226_ = lean_array_get_size(v_all_225_);
v___x_227_ = lean_nat_dec_lt(v_idx_224_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_j_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_228_ = lean_nat_sub(v_idx_224_, v___x_226_);
v___x_229_ = lean_unsigned_to_nat(1u);
v_j_230_ = lean_nat_add(v___x_228_, v___x_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_223_, v___x_231_);
v___x_233_ = lean_name_append_index_after(v___x_232_, v_j_230_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_array_fget_borrowed(v_all_225_, v_idx_224_);
lean_inc(v___x_234_);
v___x_235_ = l_Lean_mkBRecOnName(v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName___boxed(lean_object* v_info_236_, lean_object* v_idx_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_info_236_, v_idx_237_);
lean_dec(v_idx_237_);
lean_dec_ref(v_info_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_dec(v_x_247_);
return v_x_248_;
}
else
{
lean_object* v_head_250_; lean_object* v_tail_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_262_; 
v_head_250_ = lean_ctor_get(v_x_249_, 0);
v_tail_251_ = lean_ctor_get(v_x_249_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_253_ = v_x_249_;
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_tail_251_);
lean_inc(v_head_250_);
lean_dec(v_x_249_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
lean_inc(v_x_247_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 5);
lean_ctor_set(v___x_253_, 1, v_x_247_);
lean_ctor_set(v___x_253_, 0, v_x_248_);
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_x_248_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_x_247_);
v___x_256_ = v_reuseFailAlloc_261_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l_Lean_instReprExpr_repr(v_head_250_, v___x_257_);
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_256_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v_x_248_ = v___x_259_;
v_x_249_ = v_tail_251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_dec(v_x_263_);
return v_x_264_;
}
else
{
lean_object* v_head_266_; lean_object* v_tail_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
v_head_266_ = lean_ctor_get(v_x_265_, 0);
v_tail_267_ = lean_ctor_get(v_x_265_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_278_ == 0)
{
v___x_269_ = v_x_265_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_tail_267_);
lean_inc(v_head_266_);
lean_dec(v_x_265_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
lean_inc(v_x_263_);
if (v_isShared_270_ == 0)
{
lean_ctor_set_tag(v___x_269_, 5);
lean_ctor_set(v___x_269_, 1, v_x_263_);
lean_ctor_set(v___x_269_, 0, v_x_264_);
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_x_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_x_263_);
v___x_272_ = v_reuseFailAlloc_277_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Lean_instReprExpr_repr(v_head_266_, v___x_273_);
v___x_275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_272_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4_spec__6(v_x_263_, v___x_275_, v_tail_267_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(lean_object* v___y_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = l_Lean_instReprExpr_repr(v___y_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v___x_284_; 
lean_dec(v_x_283_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v_tail_285_; 
v_tail_285_ = lean_ctor_get(v_x_282_, 1);
if (lean_obj_tag(v_tail_285_) == 0)
{
lean_object* v_head_286_; lean_object* v___x_287_; 
lean_dec(v_x_283_);
v_head_286_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_head_286_);
lean_dec_ref_known(v_x_282_, 2);
v___x_287_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_286_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc(v_tail_285_);
v_head_288_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_head_288_);
lean_dec_ref_known(v_x_282_, 2);
v___x_289_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2___lam__0(v_head_288_);
v___x_290_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2_spec__4(v_x_283_, v___x_289_, v_tail_285_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(lean_object* v_xs_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_array_get_size(v_xs_291_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_dec_eq(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_295_ = lean_array_to_list(v_xs_291_);
v___x_296_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_297_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1_spec__2(v___x_295_, v___x_296_);
v___x_298_ = lean_obj_once(&l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__6);
v___x_299_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__7));
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_297_);
v___x_301_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_298_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = l_Std_Format_fill(v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_dec_ref(v_xs_291_);
v___x_305_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__10));
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_dec(v_x_306_);
return v_x_307_;
}
else
{
lean_object* v_head_309_; lean_object* v_tail_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_321_; 
v_head_309_ = lean_ctor_get(v_x_308_, 0);
v_tail_310_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_321_ == 0)
{
v___x_312_ = v_x_308_;
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_tail_310_);
lean_inc(v_head_309_);
lean_dec(v_x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
lean_inc(v_x_306_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 5);
lean_ctor_set(v___x_312_, 1, v_x_306_);
lean_ctor_set(v___x_312_, 0, v_x_307_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_x_307_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_x_306_);
v___x_315_ = v_reuseFailAlloc_320_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = l_Lean_instReprLevel_repr(v_head_309_, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_315_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v_x_307_ = v___x_318_;
v_x_308_ = v_tail_310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_dec(v_x_322_);
return v_x_323_;
}
else
{
lean_object* v_head_325_; lean_object* v_tail_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_337_; 
v_head_325_ = lean_ctor_get(v_x_324_, 0);
v_tail_326_ = lean_ctor_get(v_x_324_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_337_ == 0)
{
v___x_328_ = v_x_324_;
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_tail_326_);
lean_inc(v_head_325_);
lean_dec(v_x_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
lean_inc(v_x_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 5);
lean_ctor_set(v___x_328_, 1, v_x_322_);
lean_ctor_set(v___x_328_, 0, v_x_323_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_x_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_x_322_);
v___x_331_ = v_reuseFailAlloc_336_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = l_Lean_instReprLevel_repr(v_head_325_, v___x_332_);
v___x_334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_331_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1_spec__3(v_x_322_, v___x_334_, v_tail_326_);
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(lean_object* v___y_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = l_Lean_instReprLevel_repr(v___y_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v___x_343_; 
lean_dec(v_x_342_);
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v_tail_344_; 
v_tail_344_ = lean_ctor_get(v_x_341_, 1);
if (lean_obj_tag(v_tail_344_) == 0)
{
lean_object* v_head_345_; lean_object* v___x_346_; 
lean_dec(v_x_342_);
v_head_345_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_head_345_);
lean_dec_ref_known(v_x_341_, 2);
v___x_346_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_345_);
return v___x_346_;
}
else
{
lean_object* v_head_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_inc(v_tail_344_);
v_head_347_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_head_347_);
lean_dec_ref_known(v_x_341_, 2);
v___x_348_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0___lam__0(v_head_347_);
v___x_349_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0_spec__1(v_x_342_, v___x_348_, v_tail_344_);
return v___x_349_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__2));
v___x_355_ = lean_string_length(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3, &l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__3);
v___x_357_ = lean_nat_to_int(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(lean_object* v_a_360_){
_start:
{
if (lean_obj_tag(v_a_360_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__1));
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v___x_362_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__3));
v___x_363_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0_spec__0(v_a_360_, v___x_362_);
v___x_364_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__4);
v___x_365_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg___closed__5));
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_363_);
v___x_367_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__8));
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_364_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = 0;
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
return v___x_371_;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(18u);
v___x_382_ = lean_nat_to_int(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(10u);
v___x_387_ = lean_nat_to_int(v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(lean_object* v_x_391_){
_start:
{
lean_object* v_toIndGroupInfo_392_; lean_object* v_levels_393_; lean_object* v_params_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_toIndGroupInfo_392_ = lean_ctor_get(v_x_391_, 0);
lean_inc_ref(v_toIndGroupInfo_392_);
v_levels_393_ = lean_ctor_get(v_x_391_, 1);
lean_inc(v_levels_393_);
v_params_394_ = lean_ctor_get(v_x_391_, 2);
lean_inc_ref(v_params_394_);
lean_dec_ref(v_x_391_);
v___x_395_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__5));
v___x_396_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__3));
v___x_397_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4, &l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4_once, _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__4);
v___x_398_ = l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg(v_toIndGroupInfo_392_);
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = 0;
v___x_401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_400_);
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_396_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = ((lean_object*)(l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInfo_repr_spec__0___closed__2));
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_box(1);
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__6));
v___x_408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_395_);
v___x_410_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7, &l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7_once, _init_l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__7);
v___x_411_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(v_levels_393_);
v___x_412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_400_);
v___x_414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_409_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_403_);
v___x_416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_405_);
v___x_417_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg___closed__9));
v___x_418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_395_);
v___x_420_ = l_Array_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__1(v_params_394_);
v___x_421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_410_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1, v___x_400_);
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_419_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_obj_once(&l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13, &l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13_once, _init_l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__13);
v___x_425_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__14));
v___x_426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_423_);
v___x_427_ = ((lean_object*)(l_Lean_Elab_Structural_instReprIndGroupInfo_repr___redArg___closed__15));
v___x_428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_424_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_400_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr(lean_object* v_x_431_, lean_object* v_prec_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_x_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instReprIndGroupInst_repr___boxed(lean_object* v_x_434_, lean_object* v_prec_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr(v_x_434_, v_prec_435_);
lean_dec(v_prec_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(lean_object* v_a_437_, lean_object* v_n_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___redArg(v_a_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0___boxed(lean_object* v_a_440_, lean_object* v_n_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_List_repr___at___00Lean_Elab_Structural_instReprIndGroupInst_repr_spec__0(v_a_440_, v_n_441_);
lean_dec(v_n_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object* v_igi_445_){
_start:
{
lean_object* v_toIndGroupInfo_446_; lean_object* v_levels_447_; lean_object* v_params_448_; lean_object* v_all_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_toIndGroupInfo_446_ = lean_ctor_get(v_igi_445_, 0);
lean_inc_ref(v_toIndGroupInfo_446_);
v_levels_447_ = lean_ctor_get(v_igi_445_, 1);
lean_inc(v_levels_447_);
v_params_448_ = lean_ctor_get(v_igi_445_, 2);
lean_inc_ref(v_params_448_);
lean_dec_ref(v_igi_445_);
v_all_449_ = lean_ctor_get(v_toIndGroupInfo_446_, 0);
lean_inc_ref(v_all_449_);
lean_dec_ref(v_toIndGroupInfo_446_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_array_get(v___x_450_, v_all_449_, v___x_451_);
lean_dec_ref(v_all_449_);
v___x_453_ = l_Lean_Expr_const___override(v___x_452_, v_levels_447_);
v___x_454_ = l_Lean_mkAppN(v___x_453_, v_params_448_);
lean_dec_ref(v_params_448_);
v___x_455_ = l_Lean_MessageData_ofExpr(v___x_454_);
return v___x_455_;
}
}
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(uint8_t v___x_458_, uint8_t v_____do__lift_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
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
LEAN_EXPORT void l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_458_ = stack[0].m_num;
uint8_t v_____do__lift_459_ = stack[1].m_num;
lean_object* v___y_460_ = stack[2].m_obj;
lean_object* v___y_461_ = stack[3].m_obj;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v_res_470_;
v_res_470_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(v___x_458_, v_____do__lift_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0___boxed(lean_object* v___x_471_, lean_object* v_____do__lift_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
uint8_t v___x_1782__boxed_478_; uint8_t v_____do__lift_1783__boxed_479_; lean_object* v_res_480_; 
v___x_1782__boxed_478_ = lean_unbox(v___x_471_);
v_____do__lift_1783__boxed_479_ = lean_unbox(v_____do__lift_472_);
v_res_480_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(v___x_1782__boxed_478_, v_____do__lift_1783__boxed_479_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_480_;
}
}
uint8_t l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 1;
return v___x_482_;
}
else
{
lean_object* v_head_483_; lean_object* v_tail_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; uint8_t v___x_487_; 
v_head_483_ = lean_ctor_get(v_x_481_, 0);
v_tail_484_ = lean_ctor_get(v_x_481_, 1);
v_fst_485_ = lean_ctor_get(v_head_483_, 0);
v_snd_486_ = lean_ctor_get(v_head_483_, 1);
v___x_487_ = l_Lean_Level_isEquiv(v_fst_485_, v_snd_486_);
if (v___x_487_ == 0)
{
return v___x_487_;
}
else
{
v_x_481_ = v_tail_484_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_481_ = stack[0].m_obj;
uint8_t v_res_489_;
v_res_489_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v_x_481_);
stack->m_num = v_res_489_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0___boxed(lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v_x_490_);
lean_dec(v_x_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; uint8_t v___x_511_; uint8_t v___x_512_; uint8_t v_a_514_; lean_object* v___x_517_; 
v___x_508_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
v_fst_509_ = lean_ctor_get(v___x_508_, 0);
v_snd_510_ = lean_ctor_get(v___x_508_, 1);
v___x_511_ = lean_nat_dec_eq(v___x_493_, v___x_494_);
v___x_512_ = 1;
lean_inc(v_snd_510_);
lean_inc(v_fst_509_);
v___x_517_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_509_, v_snd_510_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; uint8_t v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_519_ == 0)
{
v_a_514_ = v___x_511_;
goto v___jp_513_;
}
else
{
goto v___jp_503_;
}
}
else
{
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_520_; uint8_t v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_517_, 1);
v___x_521_ = lean_unbox(v_a_520_);
lean_dec(v_a_520_);
v_a_514_ = v___x_521_;
goto v___jp_513_;
}
else
{
return v___x_517_;
}
}
v___jp_513_:
{
if (v_a_514_ == 0)
{
goto v___jp_503_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_box(v___x_512_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
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
v___jp_503_:
{
size_t v___x_504_; size_t v___x_505_; 
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_496_, v___x_504_);
v_i_496_ = v___x_505_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_493_ = stack[0].m_obj;
lean_object* v___x_494_ = stack[1].m_obj;
lean_object* v_as_495_ = stack[2].m_obj;
size_t v_i_496_ = stack[3].m_num;
size_t v_stop_497_ = stack[4].m_num;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v___y_500_ = stack[7].m_obj;
lean_object* v___y_501_ = stack[8].m_obj;
lean_object* v_res_525_;
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_493_, v___x_494_, v_as_495_, v_i_496_, v_stop_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1___boxed(lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_as_528_, lean_object* v_i_529_, lean_object* v_stop_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
size_t v_i_boxed_536_; size_t v_stop_boxed_537_; lean_object* v_res_538_; 
v_i_boxed_536_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_stop_boxed_537_ = lean_unbox_usize(v_stop_530_);
lean_dec(v_stop_530_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_526_, v___x_527_, v_as_528_, v_i_boxed_536_, v_stop_boxed_537_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_as_528_);
lean_dec(v___x_527_);
lean_dec(v___x_526_);
return v_res_538_;
}
}
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object* v_igi1_539_, lean_object* v_igi2_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_toIndGroupInfo_546_; lean_object* v_levels_547_; lean_object* v_params_548_; lean_object* v_toIndGroupInfo_549_; lean_object* v_levels_550_; lean_object* v_params_551_; uint8_t v___x_552_; 
v_toIndGroupInfo_546_ = lean_ctor_get(v_igi1_539_, 0);
lean_inc_ref(v_toIndGroupInfo_546_);
v_levels_547_ = lean_ctor_get(v_igi1_539_, 1);
lean_inc(v_levels_547_);
v_params_548_ = lean_ctor_get(v_igi1_539_, 2);
lean_inc_ref(v_params_548_);
lean_dec_ref(v_igi1_539_);
v_toIndGroupInfo_549_ = lean_ctor_get(v_igi2_540_, 0);
lean_inc_ref(v_toIndGroupInfo_549_);
v_levels_550_ = lean_ctor_get(v_igi2_540_, 1);
lean_inc(v_levels_550_);
v_params_551_ = lean_ctor_get(v_igi2_540_, 2);
lean_inc_ref(v_params_551_);
lean_dec_ref(v_igi2_540_);
v___x_552_ = l_Lean_Elab_Structural_instBEqIndGroupInfo_beq(v_toIndGroupInfo_546_, v_toIndGroupInfo_549_);
lean_dec_ref(v_toIndGroupInfo_549_);
lean_dec_ref(v_toIndGroupInfo_546_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v_params_551_);
lean_dec(v_levels_550_);
lean_dec_ref(v_params_548_);
lean_dec(v_levels_547_);
v___x_553_ = lean_box(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_List_lengthTR___redArg(v_levels_547_);
v___x_556_ = l_List_lengthTR___redArg(v_levels_550_);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
lean_dec(v___x_556_);
lean_dec(v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_params_551_);
lean_dec(v_levels_550_);
lean_dec_ref(v_params_548_);
lean_dec(v_levels_547_);
v___x_558_ = lean_box(v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_levels_547_, v_levels_550_);
v___x_561_ = l_List_all___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__0(v___x_560_);
lean_dec(v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v_params_551_);
lean_dec_ref(v_params_548_);
v___x_562_ = lean_box(v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___y_568_; 
v___x_564_ = lean_array_get_size(v_params_548_);
v___x_565_ = lean_array_get_size(v_params_551_);
v___x_566_ = lean_nat_dec_eq(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v_params_551_);
lean_dec_ref(v_params_548_);
v___x_580_ = lean_box(v___x_566_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_582_ = l_Array_zip___redArg(v_params_548_, v_params_551_);
lean_dec_ref(v_params_551_);
lean_dec_ref(v_params_548_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_array_get_size(v___x_582_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec_ref(v___x_582_);
v___x_586_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(v___x_566_, v___x_585_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
v___y_568_ = v___x_586_;
goto v___jp_567_;
}
else
{
if (v___x_585_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec_ref(v___x_582_);
v___x_587_ = lean_box(v___x_566_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_584_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_IndGroupInst_isDefEq_spec__1(v___x_564_, v___x_565_, v___x_582_, v___x_589_, v___x_590_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec_ref(v___x_582_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; uint8_t v___x_593_; lean_object* v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = lean_unbox(v_a_592_);
lean_dec(v_a_592_);
v___x_594_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq___lam__0(v___x_566_, v___x_593_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
v___y_568_ = v___x_594_;
goto v___jp_567_;
}
else
{
v___y_568_ = v___x_591_;
goto v___jp_567_;
}
}
}
}
v___jp_567_:
{
if (lean_obj_tag(v___y_568_) == 0)
{
lean_object* v_a_569_; uint8_t v___x_570_; 
v_a_569_ = lean_ctor_get(v___y_568_, 0);
v___x_570_ = lean_unbox(v_a_569_);
if (v___x_570_ == 0)
{
return v___y_568_;
}
else
{
lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
v_isSharedCheck_578_ = !lean_is_exclusive(v___y_568_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___y_568_, 0);
lean_dec(v_unused_579_);
v___x_572_ = v___y_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_dec(v___y_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_box(v___x_566_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
return v___y_568_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_IndGroupInst_isDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_igi1_539_ = stack[0].m_obj;
lean_object* v_igi2_540_ = stack[1].m_obj;
lean_object* v_a_541_ = stack[2].m_obj;
lean_object* v_a_542_ = stack[3].m_obj;
lean_object* v_a_543_ = stack[4].m_obj;
lean_object* v_a_544_ = stack[5].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_igi1_539_, v_igi2_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(lean_object* v_igi1_596_, lean_object* v_igi2_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_igi1_596_, v_igi2_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn(lean_object* v_group_604_, lean_object* v_lvl_605_, lean_object* v_idx_606_){
_start:
{
lean_object* v_toIndGroupInfo_607_; lean_object* v_levels_608_; lean_object* v_params_609_; lean_object* v_n_610_; lean_object* v_us_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_toIndGroupInfo_607_ = lean_ctor_get(v_group_604_, 0);
v_levels_608_ = lean_ctor_get(v_group_604_, 1);
v_params_609_ = lean_ctor_get(v_group_604_, 2);
v_n_610_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_607_, v_idx_606_);
lean_inc(v_levels_608_);
v_us_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_611_, 0, v_lvl_605_);
lean_ctor_set(v_us_611_, 1, v_levels_608_);
v___x_612_ = l_Lean_Expr_const___override(v_n_610_, v_us_611_);
v___x_613_ = l_Lean_mkAppN(v___x_612_, v_params_609_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_brecOn___boxed(lean_object* v_group_614_, lean_object* v_lvl_615_, lean_object* v_idx_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Structural_IndGroupInst_brecOn(v_group_614_, v_lvl_615_, v_idx_616_);
lean_dec(v_idx_616_);
lean_dec_ref(v_group_614_);
return v_res_617_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_893__overap_626_; lean_object* v___x_627_; 
v___f_625_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0));
v___x_893__overap_626_ = lean_panic_fn_borrowed(v___f_625_, v_msg_619_);
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
v___x_627_ = lean_apply_5(v___x_893__overap_626_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, lean_box(0));
return v___x_627_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_619_ = stack[0].m_obj;
lean_object* v___y_620_ = stack[1].m_obj;
lean_object* v___y_621_ = stack[2].m_obj;
lean_object* v___y_622_ = stack[3].m_obj;
lean_object* v___y_623_ = stack[4].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v_msg_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___boxed(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(lean_object* v_k_636_, lean_object* v_b_637_, lean_object* v_c_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
lean_inc(v___y_640_);
lean_inc_ref(v___y_639_);
v___x_644_ = lean_apply_7(v_k_636_, v_b_637_, v_c_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, lean_box(0));
return v___x_644_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_636_ = stack[0].m_obj;
lean_object* v_b_637_ = stack[1].m_obj;
lean_object* v_c_638_ = stack[2].m_obj;
lean_object* v___y_639_ = stack[3].m_obj;
lean_object* v___y_640_ = stack[4].m_obj;
lean_object* v___y_641_ = stack[5].m_obj;
lean_object* v___y_642_ = stack[6].m_obj;
lean_object* v_res_645_;
v_res_645_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(v_k_636_, v_b_637_, v_c_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed(lean_object* v_k_646_, lean_object* v_b_647_, lean_object* v_c_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0(v_k_646_, v_b_647_, v_c_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(lean_object* v_type_655_, lean_object* v_k_656_, uint8_t v_cleanupAnnotations_657_, uint8_t v_whnfType_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___f_664_; lean_object* v___x_665_; 
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_664_, 0, v_k_656_);
v___x_665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_655_, v___f_664_, v_cleanupAnnotations_657_, v_whnfType_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_665_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_665_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_655_ = stack[0].m_obj;
lean_object* v_k_656_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_657_ = stack[2].m_num;
uint8_t v_whnfType_658_ = stack[3].m_num;
lean_object* v___y_659_ = stack[4].m_obj;
lean_object* v___y_660_ = stack[5].m_obj;
lean_object* v___y_661_ = stack[6].m_obj;
lean_object* v___y_662_ = stack[7].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_655_, v_k_656_, v_cleanupAnnotations_657_, v_whnfType_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
stack->m_obj
 = v_res_682_;
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(lean_object* v_00_u03b1_695_, lean_object* v_type_696_, lean_object* v_k_697_, uint8_t v_cleanupAnnotations_698_, uint8_t v_whnfType_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_type_696_, v_k_697_, v_cleanupAnnotations_698_, v_whnfType_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_696_ = stack[1].m_obj;
lean_object* v_k_697_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_698_ = stack[3].m_num;
uint8_t v_whnfType_699_ = stack[4].m_num;
lean_object* v___y_700_ = stack[5].m_obj;
lean_object* v___y_701_ = stack[6].m_obj;
lean_object* v___y_702_ = stack[7].m_obj;
lean_object* v___y_703_ = stack[8].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(lean_box(0), v_type_696_, v_k_697_, v_cleanupAnnotations_698_, v_whnfType_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___boxed(lean_object* v_00_u03b1_707_, lean_object* v_type_708_, lean_object* v_k_709_, lean_object* v_cleanupAnnotations_710_, lean_object* v_whnfType_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_717_; uint8_t v_whnfType_boxed_718_; lean_object* v_res_719_; 
v_cleanupAnnotations_boxed_717_ = lean_unbox(v_cleanupAnnotations_710_);
v_whnfType_boxed_718_ = lean_unbox(v_whnfType_711_);
v_res_719_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1(v_00_u03b1_707_, v_type_708_, v_k_709_, v_cleanupAnnotations_boxed_717_, v_whnfType_boxed_718_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_719_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___f_726_; lean_object* v___x_1959__overap_727_; lean_object* v___x_728_; 
v___f_726_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0___closed__0));
v___x_1959__overap_727_ = lean_panic_fn_borrowed(v___f_726_, v_msg_720_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
v___x_728_ = lean_apply_5(v___x_1959__overap_727_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, lean_box(0));
return v___x_728_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_720_ = stack[0].m_obj;
lean_object* v___y_721_ = stack[1].m_obj;
lean_object* v___y_722_ = stack[2].m_obj;
lean_object* v___y_723_ = stack[3].m_obj;
lean_object* v___y_724_ = stack[4].m_obj;
lean_object* v_res_729_;
v_res_729_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
stack->m_obj
 = v_res_729_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4___boxed(lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v_msg_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_736_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__2));
v___x_741_ = lean_unsigned_to_nat(6u);
v___x_742_ = lean_unsigned_to_nat(113u);
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1));
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0));
v___x_745_ = l_mkPanicMessageWithDecl(v___x_744_, v___x_743_, v___x_742_, v___x_741_, v___x_740_);
return v___x_745_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(lean_object* v___x_746_, lean_object* v___x_747_, uint8_t v___x_748_, lean_object* v_xs_749_, lean_object* v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_array_get_size(v_xs_749_);
v___x_757_ = lean_nat_dec_lt(v___x_746_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v_xs_749_);
v___x_758_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__3);
v___x_759_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__0(v___x_758_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_sub(v___x_756_, v___x_760_);
v___x_762_ = lean_array_get_borrowed(v___x_747_, v_xs_749_, v___x_761_);
lean_dec(v___x_761_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___x_762_);
v___x_763_ = lean_infer_type(v___x_762_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = lean_array_pop(v_xs_749_);
v___x_766_ = 1;
v___x_767_ = l_Lean_Meta_mkForallFVars(v___x_765_, v_a_764_, v___x_748_, v___x_757_, v___x_757_, v___x_766_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v___x_765_);
return v___x_767_;
}
else
{
lean_dec_ref(v_xs_749_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_746_ = stack[0].m_obj;
lean_object* v___x_747_ = stack[1].m_obj;
uint8_t v___x_748_ = stack[2].m_num;
lean_object* v_xs_749_ = stack[3].m_obj;
lean_object* v_x_750_ = stack[4].m_obj;
lean_object* v___y_751_ = stack[5].m_obj;
lean_object* v___y_752_ = stack[6].m_obj;
lean_object* v___y_753_ = stack[7].m_obj;
lean_object* v___y_754_ = stack[8].m_obj;
lean_object* v_res_768_;
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(v___x_746_, v___x_747_, v___x_748_, v_xs_749_, v_x_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed(lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v_xs_772_, lean_object* v_x_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v___x_3404__boxed_779_; lean_object* v_res_780_; 
v___x_3404__boxed_779_ = lean_unbox(v___x_771_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0(v___x_769_, v___x_770_, v___x_3404__boxed_779_, v_xs_772_, v_x_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v_x_773_);
lean_dec_ref(v___x_770_);
lean_dec(v___x_769_);
return v_res_780_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(lean_object* v___x_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_bs_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_bs_784_);
return v___x_791_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v_v_797_; lean_object* v_bs_x27_798_; lean_object* v___x_799_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = l_Lean_instInhabitedExpr;
v___x_794_ = lean_nat_dec_eq(v___x_781_, v___x_792_);
v___x_795_ = lean_box(v___x_794_);
v___f_796_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___boxed), 10, 3);
lean_closure_set(v___f_796_, 0, v___x_792_);
lean_closure_set(v___f_796_, 1, v___x_793_);
lean_closure_set(v___f_796_, 2, v___x_795_);
v_v_797_ = lean_array_uget(v_bs_784_, v_i_783_);
v_bs_x27_798_ = lean_array_uset(v_bs_784_, v_i_783_, v___x_792_);
v___x_799_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__1___redArg(v_v_797_, v___f_796_, v___x_794_, v___x_794_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_783_, v___x_801_);
v___x_803_ = lean_array_uset(v_bs_x27_798_, v_i_783_, v_a_800_);
v_i_783_ = v___x_802_;
v_bs_784_ = v___x_803_;
goto _start;
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_bs_x27_798_);
v_a_805_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_799_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_799_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_781_ = stack[0].m_obj;
size_t v_sz_782_ = stack[1].m_num;
size_t v_i_783_ = stack[2].m_num;
lean_object* v_bs_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v___y_786_ = stack[5].m_obj;
lean_object* v___y_787_ = stack[6].m_obj;
lean_object* v___y_788_ = stack[7].m_obj;
lean_object* v_res_813_;
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v___x_781_, v_sz_782_, v_i_783_, v_bs_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___boxed(lean_object* v___x_814_, lean_object* v_sz_815_, lean_object* v_i_816_, lean_object* v_bs_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
size_t v_sz_boxed_823_; size_t v_i_boxed_824_; lean_object* v_res_825_; 
v_sz_boxed_823_ = lean_unbox_usize(v_sz_815_);
lean_dec(v_sz_815_);
v_i_boxed_824_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v___x_814_, v_sz_boxed_823_, v_i_boxed_824_, v_bs_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___x_814_);
return v_res_825_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_instMonadEIO___redArg();
return v___x_826_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_toApplicative_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_900_; 
v___x_837_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__0);
v___x_838_ = l_StateRefT_x27_instMonad___redArg(v___x_837_);
v_toApplicative_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_838_, 1);
lean_dec(v_unused_901_);
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_900_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_toApplicative_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_900_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_toFunctor_843_; lean_object* v_toSeq_844_; lean_object* v_toSeqLeft_845_; lean_object* v_toSeqRight_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_898_; 
v_toFunctor_843_ = lean_ctor_get(v_toApplicative_839_, 0);
v_toSeq_844_ = lean_ctor_get(v_toApplicative_839_, 2);
v_toSeqLeft_845_ = lean_ctor_get(v_toApplicative_839_, 3);
v_toSeqRight_846_ = lean_ctor_get(v_toApplicative_839_, 4);
v_isSharedCheck_898_ = !lean_is_exclusive(v_toApplicative_839_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_toApplicative_839_, 1);
lean_dec(v_unused_899_);
v___x_848_ = v_toApplicative_839_;
v_isShared_849_ = v_isSharedCheck_898_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_toSeqRight_846_);
lean_inc(v_toSeqLeft_845_);
lean_inc(v_toSeq_844_);
lean_inc(v_toFunctor_843_);
lean_dec(v_toApplicative_839_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_898_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___x_859_; 
v___f_850_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__1));
v___f_851_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_843_);
v___f_852_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_852_, 0, v_toFunctor_843_);
v___f_853_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_853_, 0, v_toFunctor_843_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___f_852_);
lean_ctor_set(v___x_854_, 1, v___f_853_);
v___f_855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_855_, 0, v_toSeqRight_846_);
v___f_856_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_856_, 0, v_toSeqLeft_845_);
v___f_857_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_857_, 0, v_toSeq_844_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 4, v___f_855_);
lean_ctor_set(v___x_848_, 3, v___f_856_);
lean_ctor_set(v___x_848_, 2, v___f_857_);
lean_ctor_set(v___x_848_, 1, v___f_850_);
lean_ctor_set(v___x_848_, 0, v___x_854_);
v___x_859_ = v___x_848_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___f_850_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v___f_857_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v___f_856_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v___f_855_);
v___x_859_ = v_reuseFailAlloc_897_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___f_851_);
lean_ctor_set(v___x_841_, 0, v___x_859_);
v___x_861_ = v___x_841_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___f_851_);
v___x_861_ = v_reuseFailAlloc_896_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v_toApplicative_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_894_; 
v___x_862_ = l_StateRefT_x27_instMonad___redArg(v___x_861_);
v_toApplicative_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_862_, 1);
lean_dec(v_unused_895_);
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_894_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_toApplicative_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_894_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_toFunctor_867_; lean_object* v_toSeq_868_; lean_object* v_toSeqLeft_869_; lean_object* v_toSeqRight_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_892_; 
v_toFunctor_867_ = lean_ctor_get(v_toApplicative_863_, 0);
v_toSeq_868_ = lean_ctor_get(v_toApplicative_863_, 2);
v_toSeqLeft_869_ = lean_ctor_get(v_toApplicative_863_, 3);
v_toSeqRight_870_ = lean_ctor_get(v_toApplicative_863_, 4);
v_isSharedCheck_892_ = !lean_is_exclusive(v_toApplicative_863_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_toApplicative_863_, 1);
lean_dec(v_unused_893_);
v___x_872_ = v_toApplicative_863_;
v_isShared_873_ = v_isSharedCheck_892_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_toSeqRight_870_);
lean_inc(v_toSeqLeft_869_);
lean_inc(v_toSeq_868_);
lean_inc(v_toFunctor_867_);
lean_dec(v_toApplicative_863_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_892_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___x_883_; 
v___f_874_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__3));
v___f_875_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_867_);
v___f_876_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_876_, 0, v_toFunctor_867_);
v___f_877_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_877_, 0, v_toFunctor_867_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___f_876_);
lean_ctor_set(v___x_878_, 1, v___f_877_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_879_, 0, v_toSeqRight_870_);
v___f_880_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_880_, 0, v_toSeqLeft_869_);
v___f_881_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_881_, 0, v_toSeq_868_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 4, v___f_879_);
lean_ctor_set(v___x_872_, 3, v___f_880_);
lean_ctor_set(v___x_872_, 2, v___f_881_);
lean_ctor_set(v___x_872_, 1, v___f_874_);
lean_ctor_set(v___x_872_, 0, v___x_878_);
v___x_883_ = v___x_872_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___f_874_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___f_881_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v___f_880_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v___f_879_);
v___x_883_ = v_reuseFailAlloc_891_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___f_875_);
lean_ctor_set(v___x_865_, 0, v___x_883_);
v___x_885_ = v___x_865_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___f_875_);
v___x_885_ = v_reuseFailAlloc_890_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_2564__overap_888_; lean_object* v___x_889_; 
v___x_886_ = lean_box(0);
v___x_887_ = l_instInhabitedOfMonad___redArg(v___x_885_, v___x_886_);
v___x_2564__overap_888_ = lean_panic_fn_borrowed(v___x_887_, v_msg_831_);
lean_dec(v___x_887_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
v___x_889_ = lean_apply_5(v___x_2564__overap_888_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
return v___x_889_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_831_ = stack[0].m_obj;
lean_object* v___y_832_ = stack[1].m_obj;
lean_object* v___y_833_ = stack[2].m_obj;
lean_object* v___y_834_ = stack[3].m_obj;
lean_object* v___y_835_ = stack[4].m_obj;
lean_object* v_res_902_;
v_res_902_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
stack->m_obj
 = v_res_902_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3___boxed(lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(lean_object* v_msgData_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_env_917_; uint8_t v___x_918_; lean_object* v_env_919_; lean_object* v___x_920_; lean_object* v_toCold_921_; lean_object* v_mctx_922_; lean_object* v_lctx_923_; lean_object* v_options_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_916_ = lean_st_ref_get(v___y_914_);
v_env_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_env_917_);
lean_dec(v___x_916_);
v___x_918_ = 0;
v_env_919_ = l_Lean_Environment_setRecordingDeps(v_env_917_, v___x_918_);
v___x_920_ = lean_st_ref_get(v___y_912_);
v_toCold_921_ = lean_ctor_get(v___y_913_, 0);
v_mctx_922_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_mctx_922_);
lean_dec(v___x_920_);
v_lctx_923_ = lean_ctor_get(v___y_911_, 2);
v_options_924_ = lean_ctor_get(v_toCold_921_, 2);
lean_inc_ref(v_options_924_);
lean_inc_ref(v_lctx_923_);
v___x_925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_925_, 0, v_env_919_);
lean_ctor_set(v___x_925_, 1, v_mctx_922_);
lean_ctor_set(v___x_925_, 2, v_lctx_923_);
lean_ctor_set(v___x_925_, 3, v_options_924_);
v___x_926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v_msgData_910_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_910_ = stack[0].m_obj;
lean_object* v___y_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v___y_913_ = stack[3].m_obj;
lean_object* v___y_914_ = stack[4].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msgData_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msgData_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_935_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(lean_object* v_msg_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_ref_942_; lean_object* v___x_943_; lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_952_; 
v_ref_942_ = lean_ctor_get(v___y_939_, 2);
v___x_943_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_spec__4(v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_952_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
lean_inc(v_ref_942_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_ref_942_);
lean_ctor_set(v___x_948_, 1, v_a_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_936_ = stack[0].m_obj;
lean_object* v___y_937_ = stack[1].m_obj;
lean_object* v___y_938_ = stack[2].m_obj;
lean_object* v___y_939_ = stack[3].m_obj;
lean_object* v___y_940_ = stack[4].m_obj;
lean_object* v_res_953_;
v_res_953_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg___boxed(lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__0));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__2));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_970_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__6));
v___x_971_ = lean_unsigned_to_nat(11u);
v___x_972_ = lean_unsigned_to_nat(129u);
v___x_973_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__5));
v___x_974_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__4));
v___x_975_ = l_mkPanicMessageWithDecl(v___x_974_, v___x_973_, v___x_972_, v___x_971_, v___x_970_);
return v___x_975_;
}
}
lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(lean_object* v_constName_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_990_; lean_object* v_env_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_st_ref_get(v___y_980_);
v_env_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_ref(v_env_991_);
lean_dec(v___x_990_);
v___x_992_ = 0;
lean_inc(v_constName_976_);
v___x_993_ = l_Lean_Environment_findAsync_x3f(v_env_991_, v_constName_976_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 1)
{
lean_object* v_val_994_; uint8_t v_kind_995_; 
v_val_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v___x_993_, 1);
v_kind_995_ = lean_ctor_get_uint8(v_val_994_, sizeof(void*)*3);
if (v_kind_995_ == 7)
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_994_);
if (lean_obj_tag(v___x_996_) == 7)
{
lean_object* v_val_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_constName_976_);
v_val_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_val_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v___x_996_);
v___x_1005_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__7);
v___x_1006_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__3(v___x_1005_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_del_object(v___x_1009_);
goto v___jp_982_;
}
else
{
lean_object* v_val_1011_; lean_object* v___x_1013_; 
lean_dec(v_constName_976_);
v_val_1011_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v_a_1007_, 1);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v_val_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_val_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_constName_976_);
v_a_1016_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1006_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1006_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_dec(v_val_994_);
goto v___jp_982_;
}
}
else
{
lean_dec(v___x_993_);
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_983_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__1);
v___x_984_ = 0;
v___x_985_ = l_Lean_MessageData_ofConstName(v_constName_976_, v___x_984_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_983_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3, &l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3_once, _init_l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___closed__3);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v___x_988_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_989_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_976_ = stack[0].m_obj;
lean_object* v___y_977_ = stack[1].m_obj;
lean_object* v___y_978_ = stack[2].m_obj;
lean_object* v___y_979_ = stack[3].m_obj;
lean_object* v___y_980_ = stack[4].m_obj;
lean_object* v_res_1024_;
v_res_1024_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_constName_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
stack->m_obj
 = v_res_1024_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2___boxed(lean_object* v_constName_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_constName_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1031_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__0));
v___x_1034_ = lean_unsigned_to_nat(2u);
v___x_1035_ = lean_unsigned_to_nat(104u);
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__1));
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3___lam__0___closed__0));
v___x_1038_ = l_mkPanicMessageWithDecl(v___x_1037_, v___x_1036_, v___x_1035_, v___x_1034_, v___x_1033_);
return v___x_1038_;
}
}
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object* v_igi_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_toIndGroupInfo_1047_; lean_object* v_levels_1048_; lean_object* v_params_1049_; lean_object* v_all_1050_; lean_object* v_numNested_1051_; lean_object* v___y_1053_; lean_object* v_lower_1054_; lean_object* v_upper_1055_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_toIndGroupInfo_1047_ = lean_ctor_get(v_igi_1041_, 0);
lean_inc_ref(v_toIndGroupInfo_1047_);
v_levels_1048_ = lean_ctor_get(v_igi_1041_, 1);
lean_inc(v_levels_1048_);
v_params_1049_ = lean_ctor_get(v_igi_1041_, 2);
lean_inc_ref(v_params_1049_);
lean_dec_ref(v_igi_1041_);
v_all_1050_ = lean_ctor_get(v_toIndGroupInfo_1047_, 0);
lean_inc_ref(v_all_1050_);
v_numNested_1051_ = lean_ctor_get(v_toIndGroupInfo_1047_, 1);
lean_inc(v_numNested_1051_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_nat_dec_eq(v_numNested_1051_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_recName_1065_; lean_object* v___x_1066_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_array_get_borrowed(v___x_1063_, v_all_1050_, v___x_1061_);
lean_inc(v___x_1064_);
v_recName_1065_ = l_Lean_mkRecName(v___x_1064_);
lean_inc(v_recName_1065_);
v___x_1066_ = l_Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2(v_recName_1065_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v_toConstantVal_1068_; lean_object* v_numMotives_1069_; lean_object* v___y_1071_; lean_object* v___x_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1094_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_toConstantVal_1068_ = lean_ctor_get(v_a_1067_, 0);
lean_inc_ref(v_toConstantVal_1068_);
v_numMotives_1069_ = lean_ctor_get(v_a_1067_, 4);
lean_inc(v_numMotives_1069_);
lean_dec(v_a_1067_);
v___x_1079_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_1047_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_toIndGroupInfo_1047_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1095_ = lean_ctor_get(v_toIndGroupInfo_1047_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_toIndGroupInfo_1047_, 0);
lean_dec(v_unused_1096_);
v___x_1081_ = v_toIndGroupInfo_1047_;
v_isShared_1082_ = v_isSharedCheck_1094_;
goto v_resetjp_1080_;
}
else
{
lean_dec(v_toIndGroupInfo_1047_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1094_;
goto v_resetjp_1080_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = l_Lean_Expr_const___override(v_recName_1065_, v___y_1071_);
v___x_1073_ = l_Lean_mkAppN(v___x_1072_, v_params_1049_);
lean_dec_ref(v_params_1049_);
v___x_1074_ = l_Lean_Meta_inferArgumentTypesN(v_numMotives_1069_, v___x_1073_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = lean_array_get_size(v_all_1050_);
lean_dec_ref(v_all_1050_);
v___x_1077_ = lean_array_get_size(v_a_1075_);
v___x_1078_ = lean_nat_dec_le(v___x_1076_, v___x_1061_);
if (v___x_1078_ == 0)
{
v___y_1053_ = v_a_1075_;
v_lower_1054_ = v___x_1076_;
v_upper_1055_ = v___x_1077_;
goto v___jp_1052_;
}
else
{
v___y_1053_ = v_a_1075_;
v_lower_1054_ = v___x_1061_;
v_upper_1055_ = v___x_1077_;
goto v___jp_1052_;
}
}
else
{
lean_dec(v_numNested_1051_);
lean_dec_ref(v_all_1050_);
return v___x_1074_;
}
}
v_resetjp_1080_:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_eq(v_numMotives_1069_, v___x_1079_);
lean_dec(v___x_1079_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_del_object(v___x_1081_);
lean_dec(v_numMotives_1069_);
lean_dec_ref(v_toConstantVal_1068_);
lean_dec(v_recName_1065_);
lean_dec(v_numNested_1051_);
lean_dec_ref(v_all_1050_);
lean_dec_ref(v_params_1049_);
lean_dec(v_levels_1048_);
v___x_1084_ = lean_obj_once(&l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1, &l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1_once, _init_l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__1);
v___x_1085_ = l_panic___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__4(v___x_1084_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v___x_1085_;
}
else
{
lean_object* v_levelParams_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_levelParams_1086_ = lean_ctor_get(v_toConstantVal_1068_, 1);
lean_inc(v_levelParams_1086_);
lean_dec_ref(v_toConstantVal_1068_);
v___x_1087_ = l_List_lengthTR___redArg(v_levels_1048_);
v___x_1088_ = l_List_lengthTR___redArg(v_levelParams_1086_);
lean_dec(v_levelParams_1086_);
v___x_1089_ = lean_nat_dec_eq(v___x_1087_, v___x_1088_);
lean_dec(v___x_1088_);
lean_dec(v___x_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 1);
lean_ctor_set(v___x_1081_, 1, v_levels_1048_);
lean_ctor_set(v___x_1081_, 0, v___x_1090_);
v___x_1092_ = v___x_1081_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_levels_1048_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v___y_1071_ = v___x_1092_;
goto v___jp_1070_;
}
}
else
{
lean_del_object(v___x_1081_);
v___y_1071_ = v_levels_1048_;
goto v___jp_1070_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_recName_1065_);
lean_dec(v_numNested_1051_);
lean_dec_ref(v_all_1050_);
lean_dec_ref(v_params_1049_);
lean_dec(v_levels_1048_);
lean_dec_ref(v_toIndGroupInfo_1047_);
v_a_1097_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1066_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1066_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_numNested_1051_);
lean_dec_ref(v_all_1050_);
lean_dec_ref(v_params_1049_);
lean_dec(v_levels_1048_);
lean_dec_ref(v_toIndGroupInfo_1047_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___closed__2));
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
v___jp_1052_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; size_t v_sz_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1056_ = l_Array_toSubarray___redArg(v___y_1053_, v_lower_1054_, v_upper_1055_);
v___x_1057_ = l_Subarray_copy___redArg(v___x_1056_);
v_sz_1058_ = lean_array_size(v___x_1057_);
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__3(v_numNested_1051_, v_sz_1058_, v___x_1059_, v___x_1057_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_numNested_1051_);
return v___x_1060_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_0interp(lean_interpreter_value* stack)
{
lean_object* v_igi_1041_ = stack[0].m_obj;
lean_object* v_a_1042_ = stack[1].m_obj;
lean_object* v_a_1043_ = stack[2].m_obj;
lean_object* v_a_1044_ = stack[3].m_obj;
lean_object* v_a_1045_ = stack[4].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_igi_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers___boxed(lean_object* v_igi_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_igi_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1114_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(lean_object* v_00_u03b1_1115_, lean_object* v_msg_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___redArg(v_msg_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1116_ = stack[1].m_obj;
lean_object* v___y_1117_ = stack[2].m_obj;
lean_object* v___y_1118_ = stack[3].m_obj;
lean_object* v___y_1119_ = stack[4].m_obj;
lean_object* v___y_1120_ = stack[5].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(lean_box(0), v_msg_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Elab_Structural_IndGroupInst_nestedTypeFormers_spec__2_spec__2(v_00_u03b1_1124_, v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
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
