// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Discharger
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.AppBuilder
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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
uint8_t v_contextDependent_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_contextDependent_7_ = lean_ctor_get_uint8(v_t_5_, 0);
lean_dec_ref_known(v_t_5_, 0);
v___x_8_ = lean_box(v_contextDependent_7_);
v___x_9_ = lean_apply_1(v_k_6_, v___x_8_);
return v___x_9_;
}
else
{
lean_object* v_proof_10_; uint8_t v_contextDependent_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_proof_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_proof_10_);
v_contextDependent_11_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5_, 1);
v___x_12_ = lean_box(v_contextDependent_11_);
v___x_13_ = lean_apply_2(v_k_6_, v_proof_10_, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(lean_object* v_t_26_, lean_object* v_failed_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_26_, v_failed_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_failed_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_30_, v_failed_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(lean_object* v_t_34_, lean_object* v_solved_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_34_, v_solved_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_solved_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_38_, v_solved_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(lean_object* v_e_42_, lean_object* v_result_43_){
_start:
{
if (lean_obj_tag(v_result_43_) == 0)
{
uint8_t v_contextDependent_44_; lean_object* v___x_45_; 
lean_dec_ref(v_e_42_);
v_contextDependent_44_ = lean_ctor_get_uint8(v_result_43_, 1);
lean_dec_ref_known(v_result_43_, 0);
v___x_45_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_45_, 0, v_contextDependent_44_);
return v___x_45_;
}
else
{
lean_object* v_e_x27_46_; lean_object* v_proof_47_; uint8_t v_contextDependent_48_; uint8_t v___x_49_; 
v_e_x27_46_ = lean_ctor_get(v_result_43_, 0);
lean_inc_ref(v_e_x27_46_);
v_proof_47_ = lean_ctor_get(v_result_43_, 1);
lean_inc_ref(v_proof_47_);
v_contextDependent_48_ = lean_ctor_get_uint8(v_result_43_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_result_43_, 2);
v___x_49_ = l_Lean_Expr_isTrue(v_e_x27_46_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
lean_dec_ref(v_proof_47_);
lean_dec_ref(v_e_42_);
v___x_50_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_50_, 0, v_contextDependent_48_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = l_Lean_Meta_mkOfEqTrueCore(v_e_42_, v_proof_47_);
v___x_52_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v_contextDependent_48_);
return v___x_52_;
}
}
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(lean_object* v_p_53_, lean_object* v_e_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc(v_a_61_);
lean_inc_ref(v_a_60_);
lean_inc(v_a_59_);
lean_inc_ref(v_a_58_);
lean_inc(v_a_57_);
lean_inc_ref(v_a_56_);
lean_inc(v_a_55_);
lean_inc_ref(v_e_54_);
v___x_65_ = lean_apply_11(v_p_53_, v_e_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, lean_box(0));
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_54_, v_a_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec_ref(v_e_54_);
v_a_75_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_65_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_53_ = stack[0].m_obj;
lean_object* v_e_54_ = stack[1].m_obj;
lean_object* v_a_55_ = stack[2].m_obj;
lean_object* v_a_56_ = stack[3].m_obj;
lean_object* v_a_57_ = stack[4].m_obj;
lean_object* v_a_58_ = stack[5].m_obj;
lean_object* v_a_59_ = stack[6].m_obj;
lean_object* v_a_60_ = stack[7].m_obj;
lean_object* v_a_61_ = stack[8].m_obj;
lean_object* v_a_62_ = stack[9].m_obj;
lean_object* v_a_63_ = stack[10].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(v_p_53_, v_e_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object* v_p_84_, lean_object* v_e_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(v_p_84_, v_e_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
return v_res_96_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(lean_object* v_a_97_, lean_object* v_persistentCache_98_, lean_object* v_transientCache_99_, lean_object* v_funext_100_, lean_object* v_a_x3f_101_){
_start:
{
lean_object* v___x_103_; lean_object* v_numSteps_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_114_; 
v___x_103_ = lean_st_ref_take(v_a_97_);
v_numSteps_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; lean_object* v_unused_117_; 
v_unused_115_ = lean_ctor_get(v___x_103_, 3);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v___x_103_, 2);
lean_dec(v_unused_116_);
v_unused_117_ = lean_ctor_get(v___x_103_, 1);
lean_dec(v_unused_117_);
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_numSteps_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 3, v_funext_100_);
lean_ctor_set(v___x_106_, 2, v_transientCache_99_);
lean_ctor_set(v___x_106_, 1, v_persistentCache_98_);
v___x_110_ = v___x_106_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_numSteps_104_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_persistentCache_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_transientCache_99_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_funext_100_);
v___x_110_ = v_reuseFailAlloc_113_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_st_ref_put(v_a_97_, v___x_110_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_108_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_97_ = stack[0].m_obj;
lean_object* v_persistentCache_98_ = stack[1].m_obj;
lean_object* v_transientCache_99_ = stack[2].m_obj;
lean_object* v_funext_100_ = stack[3].m_obj;
lean_object* v_a_x3f_101_ = stack[4].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_97_, v_persistentCache_98_, v_transientCache_99_, v_funext_100_, v_a_x3f_101_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(lean_object* v_a_119_, lean_object* v_persistentCache_120_, lean_object* v_transientCache_121_, lean_object* v_funext_122_, lean_object* v_a_x3f_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_119_, v_persistentCache_120_, v_transientCache_121_, v_funext_122_, v_a_x3f_123_);
lean_dec(v_a_x3f_123_);
lean_dec(v_a_119_);
return v_res_125_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf(lean_object* v_e_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_130_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_192_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_192_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_192_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_192_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_maxDischargeDepth_144_; lean_object* v_config_145_; lean_object* v_initialLCtxSize_146_; lean_object* v_dischargeDepth_147_; uint8_t v___x_148_; 
v_maxDischargeDepth_144_ = lean_ctor_get(v_a_140_, 1);
lean_inc(v_maxDischargeDepth_144_);
lean_dec(v_a_140_);
v_config_145_ = lean_ctor_get(v_a_130_, 0);
v_initialLCtxSize_146_ = lean_ctor_get(v_a_130_, 1);
v_dischargeDepth_147_ = lean_ctor_get(v_a_130_, 2);
v___x_148_ = lean_nat_dec_lt(v_maxDischargeDepth_144_, v_dischargeDepth_147_);
lean_dec(v_maxDischargeDepth_144_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v_persistentCache_150_; lean_object* v___x_151_; lean_object* v_transientCache_152_; lean_object* v___x_153_; lean_object* v_funext_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_del_object(v___x_142_);
v___x_149_ = lean_st_ref_get(v_a_131_);
v_persistentCache_150_ = lean_ctor_get(v___x_149_, 1);
lean_inc_ref(v_persistentCache_150_);
lean_dec(v___x_149_);
v___x_151_ = lean_st_ref_get(v_a_131_);
v_transientCache_152_ = lean_ctor_get(v___x_151_, 2);
lean_inc_ref(v_transientCache_152_);
lean_dec(v___x_151_);
v___x_153_ = lean_st_ref_get(v_a_131_);
v_funext_154_ = lean_ctor_get(v___x_153_, 3);
lean_inc_ref(v_funext_154_);
lean_dec(v___x_153_);
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_dischargeDepth_147_, v___x_155_);
lean_inc(v_initialLCtxSize_146_);
lean_inc_ref(v_config_145_);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v_config_145_);
lean_ctor_set(v___x_157_, 1, v_initialLCtxSize_146_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_inc(v_a_137_);
lean_inc_ref(v_a_136_);
lean_inc(v_a_135_);
lean_inc_ref(v_a_134_);
lean_inc(v_a_133_);
lean_inc_ref(v_a_132_);
lean_inc(v_a_131_);
lean_inc(v_a_129_);
lean_inc_ref(v_e_128_);
v___x_158_ = lean_sym_simp(v_e_128_, v_a_129_, v___x_157_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_176_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_176_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_176_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_176_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_128_, v_a_159_);
lean_inc_ref(v___x_163_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 1);
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_175_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v___x_166_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_131_, v_persistentCache_150_, v_transientCache_152_, v_funext_154_, v___x_165_);
lean_dec_ref(v___x_165_);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v___x_166_, 0);
lean_dec(v_unused_174_);
v___x_168_ = v___x_166_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_dec(v___x_166_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_163_);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_163_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v_e_128_);
v_a_177_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_158_, 1);
v___x_178_ = lean_box(0);
v___x_179_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_131_, v_persistentCache_150_, v_transientCache_152_, v_funext_154_, v___x_178_);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v___x_179_, 0);
lean_dec(v_unused_187_);
v___x_181_ = v___x_179_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_dec(v___x_179_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 1);
lean_ctor_set(v___x_181_, 0, v_a_177_);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_177_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec_ref(v_e_128_);
v___x_188_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0));
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_188_);
v___x_190_ = v___x_142_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_e_128_);
v_a_193_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_139_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_139_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_dischargeSimpSelf_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_128_ = stack[0].m_obj;
lean_object* v_a_129_ = stack[1].m_obj;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_a_131_ = stack[3].m_obj;
lean_object* v_a_132_ = stack[4].m_obj;
lean_object* v_a_133_ = stack[5].m_obj;
lean_object* v_a_134_ = stack[6].m_obj;
lean_object* v_a_135_ = stack[7].m_obj;
lean_object* v_a_136_ = stack[8].m_obj;
lean_object* v_a_137_ = stack[9].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf(v_e_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object* v_e_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf(v_e_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
return v_res_213_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg(){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0));
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_dischargeNone___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_217_;
v_res_217_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v_res_219_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone(lean_object* v_x_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_dischargeNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_220_ = stack[0].m_obj;
lean_object* v_a_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_a_223_ = stack[3].m_obj;
lean_object* v_a_224_ = stack[4].m_obj;
lean_object* v_a_225_ = stack[5].m_obj;
lean_object* v_a_226_ = stack[6].m_obj;
lean_object* v_a_227_ = stack[7].m_obj;
lean_object* v_a_228_ = stack[8].m_obj;
lean_object* v_a_229_ = stack[9].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_Meta_Sym_Simp_dischargeNone(v_x_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Meta_Sym_Simp_dischargeNone(v_x_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_x_233_);
return v_res_244_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(lean_object* v_e_248_, lean_object* v_as_249_, size_t v_sz_250_, size_t v_i_251_, lean_object* v_b_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_usize_dec_lt(v_i_251_, v_sz_250_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v_e_248_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_b_252_);
return v___x_259_;
}
else
{
lean_object* v_snd_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_309_; 
v_snd_260_ = lean_ctor_get(v_b_252_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_b_252_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v_b_252_, 0);
lean_dec(v_unused_310_);
v___x_262_ = v_b_252_;
v_isShared_263_ = v_isSharedCheck_309_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_snd_260_);
lean_dec(v_b_252_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_309_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v_a_266_; lean_object* v_a_273_; 
v___x_264_ = lean_box(0);
v_a_273_ = lean_array_uget(v_as_249_, v_i_251_);
if (lean_obj_tag(v_a_273_) == 0)
{
v_a_266_ = v_snd_260_;
goto v___jp_265_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_308_; 
v_val_274_ = lean_ctor_get(v_a_273_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_273_);
if (v_isSharedCheck_308_ == 0)
{
v___x_276_ = v_a_273_;
v_isShared_277_ = v_isSharedCheck_308_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_val_274_);
lean_dec(v_a_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_308_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = lean_box(0);
v___x_279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_280_ = l_Lean_LocalDecl_isAuxDecl(v_val_274_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = l_Lean_LocalDecl_type(v_val_274_);
lean_inc_ref(v_e_248_);
v___x_282_ = l_Lean_Meta_isExprDefEq(v___x_281_, v_e_248_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_299_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_299_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_299_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_299_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
uint8_t v___x_287_; 
v___x_287_ = lean_unbox(v_a_283_);
lean_dec(v_a_283_);
if (v___x_287_ == 0)
{
lean_del_object(v___x_285_);
lean_del_object(v___x_276_);
lean_dec(v_val_274_);
lean_dec(v_snd_260_);
v_a_266_ = v___x_279_;
goto v___jp_265_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
lean_del_object(v___x_262_);
lean_dec_ref(v_e_248_);
v___x_288_ = l_Lean_LocalDecl_toExpr(v_val_274_);
v___x_289_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___x_258_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_289_);
v___x_291_ = v___x_276_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_298_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_278_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_snd_260_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_294_);
v___x_296_ = v___x_285_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_del_object(v___x_276_);
lean_dec(v_val_274_);
lean_del_object(v___x_262_);
lean_dec(v_snd_260_);
lean_dec_ref(v_e_248_);
v_a_300_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_282_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_282_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_del_object(v___x_276_);
lean_dec(v_val_274_);
lean_dec(v_snd_260_);
v_a_266_ = v___x_279_;
goto v___jp_265_;
}
}
}
v___jp_265_:
{
lean_object* v___x_268_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_a_266_);
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_268_ = v___x_262_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_a_266_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
size_t v___x_269_; size_t v___x_270_; 
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_add(v_i_251_, v___x_269_);
v_i_251_ = v___x_270_;
v_b_252_ = v___x_268_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_248_ = stack[0].m_obj;
lean_object* v_as_249_ = stack[1].m_obj;
size_t v_sz_250_ = stack[2].m_num;
size_t v_i_251_ = stack[3].m_num;
lean_object* v_b_252_ = stack[4].m_obj;
lean_object* v___y_253_ = stack[5].m_obj;
lean_object* v___y_254_ = stack[6].m_obj;
lean_object* v___y_255_ = stack[7].m_obj;
lean_object* v___y_256_ = stack[8].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_248_, v_as_249_, v_sz_250_, v_i_251_, v_b_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_e_312_, lean_object* v_as_313_, lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
size_t v_sz_boxed_322_; size_t v_i_boxed_323_; lean_object* v_res_324_; 
v_sz_boxed_322_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_323_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_312_, v_as_313_, v_sz_boxed_322_, v_i_boxed_323_, v_b_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec_ref(v_as_313_);
return v_res_324_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(lean_object* v_e_325_, lean_object* v_as_326_, size_t v_sz_327_, size_t v_i_328_, lean_object* v_b_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_lt(v_i_328_, v_sz_327_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_e_325_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_b_329_);
return v___x_341_;
}
else
{
lean_object* v_snd_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_391_; 
v_snd_342_ = lean_ctor_get(v_b_329_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_b_329_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_b_329_, 0);
lean_dec(v_unused_392_);
v___x_344_ = v_b_329_;
v_isShared_345_ = v_isSharedCheck_391_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snd_342_);
lean_dec(v_b_329_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_391_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v_a_348_; lean_object* v_a_355_; 
v___x_346_ = lean_box(0);
v_a_355_ = lean_array_uget(v_as_326_, v_i_328_);
if (lean_obj_tag(v_a_355_) == 0)
{
v_a_348_ = v_snd_342_;
goto v___jp_347_;
}
else
{
lean_object* v_val_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_390_; 
v_val_356_ = lean_ctor_get(v_a_355_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_a_355_);
if (v_isSharedCheck_390_ == 0)
{
v___x_358_ = v_a_355_;
v_isShared_359_ = v_isSharedCheck_390_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_val_356_);
lean_dec(v_a_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_390_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_box(0);
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_362_ = l_Lean_LocalDecl_isAuxDecl(v_val_356_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = l_Lean_LocalDecl_type(v_val_356_);
lean_inc_ref(v_e_325_);
v___x_364_ = l_Lean_Meta_isExprDefEq(v___x_363_, v_e_325_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_381_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___x_369_; 
v___x_369_ = lean_unbox(v_a_365_);
lean_dec(v_a_365_);
if (v___x_369_ == 0)
{
lean_del_object(v___x_367_);
lean_del_object(v___x_358_);
lean_dec(v_val_356_);
lean_dec(v_snd_342_);
v_a_348_ = v___x_361_;
goto v___jp_347_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_del_object(v___x_344_);
lean_dec_ref(v_e_325_);
v___x_370_ = l_Lean_LocalDecl_toExpr(v_val_356_);
v___x_371_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_340_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_371_);
v___x_373_ = v___x_358_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_380_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_360_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_snd_342_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_376_);
v___x_378_ = v___x_367_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_del_object(v___x_358_);
lean_dec(v_val_356_);
lean_del_object(v___x_344_);
lean_dec(v_snd_342_);
lean_dec_ref(v_e_325_);
v_a_382_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_364_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_364_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_del_object(v___x_358_);
lean_dec(v_val_356_);
lean_dec(v_snd_342_);
v_a_348_ = v___x_361_;
goto v___jp_347_;
}
}
}
v___jp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_a_348_);
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_350_ = v___x_344_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_a_348_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_328_, v___x_351_);
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_325_, v_as_326_, v_sz_327_, v___x_352_, v___x_350_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_325_ = stack[0].m_obj;
lean_object* v_as_326_ = stack[1].m_obj;
size_t v_sz_327_ = stack[2].m_num;
size_t v_i_328_ = stack[3].m_num;
lean_object* v_b_329_ = stack[4].m_obj;
lean_object* v___y_330_ = stack[5].m_obj;
lean_object* v___y_331_ = stack[6].m_obj;
lean_object* v___y_332_ = stack[7].m_obj;
lean_object* v___y_333_ = stack[8].m_obj;
lean_object* v___y_334_ = stack[9].m_obj;
lean_object* v___y_335_ = stack[10].m_obj;
lean_object* v___y_336_ = stack[11].m_obj;
lean_object* v___y_337_ = stack[12].m_obj;
lean_object* v___y_338_ = stack[13].m_obj;
lean_object* v_res_393_;
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_325_, v_as_326_, v_sz_327_, v_i_328_, v_b_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(lean_object* v_e_394_, lean_object* v_as_395_, lean_object* v_sz_396_, lean_object* v_i_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
size_t v_sz_boxed_409_; size_t v_i_boxed_410_; lean_object* v_res_411_; 
v_sz_boxed_409_ = lean_unbox_usize(v_sz_396_);
lean_dec(v_sz_396_);
v_i_boxed_410_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_394_, v_as_395_, v_sz_boxed_409_, v_i_boxed_410_, v_b_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_as_395_);
return v_res_411_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_e_415_, lean_object* v_as_416_, size_t v_sz_417_, size_t v_i_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = lean_usize_dec_lt(v_i_418_, v_sz_417_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec_ref(v_e_415_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_b_419_);
return v___x_426_;
}
else
{
lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_477_; 
v_snd_427_ = lean_ctor_get(v_b_419_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_b_419_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_b_419_, 0);
lean_dec(v_unused_478_);
v___x_429_ = v_b_419_;
v_isShared_430_ = v_isSharedCheck_477_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_dec(v_b_419_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_477_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v_a_433_; lean_object* v_a_440_; 
v___x_431_ = lean_box(0);
v_a_440_ = lean_array_uget(v_as_416_, v_i_418_);
if (lean_obj_tag(v_a_440_) == 0)
{
v_a_433_ = v_snd_427_;
goto v___jp_432_;
}
else
{
lean_object* v_val_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_476_; 
v_val_441_ = lean_ctor_get(v_a_440_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_476_ == 0)
{
v___x_443_ = v_a_440_;
v_isShared_444_ = v_isSharedCheck_476_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_val_441_);
lean_dec(v_a_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_476_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_box(0);
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_447_ = l_Lean_LocalDecl_isAuxDecl(v_val_441_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_Lean_LocalDecl_type(v_val_441_);
lean_inc_ref(v_e_415_);
v___x_449_ = l_Lean_Meta_isExprDefEq(v___x_448_, v_e_415_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_467_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_467_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_467_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_467_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_unbox(v_a_450_);
lean_dec(v_a_450_);
if (v___x_454_ == 0)
{
lean_del_object(v___x_452_);
lean_del_object(v___x_443_);
lean_dec(v_val_441_);
lean_dec(v_snd_427_);
v_a_433_ = v___x_446_;
goto v___jp_432_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_del_object(v___x_429_);
lean_dec_ref(v_e_415_);
v___x_455_ = l_Lean_LocalDecl_toExpr(v_val_441_);
v___x_456_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*1, v___x_425_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_456_);
v___x_458_ = v___x_443_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_466_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_445_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_snd_427_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_462_);
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_del_object(v___x_443_);
lean_dec(v_val_441_);
lean_del_object(v___x_429_);
lean_dec(v_snd_427_);
lean_dec_ref(v_e_415_);
v_a_468_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_449_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_449_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_del_object(v___x_443_);
lean_dec(v_val_441_);
lean_dec(v_snd_427_);
v_a_433_ = v___x_446_;
goto v___jp_432_;
}
}
}
v___jp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_a_433_);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_a_433_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
size_t v___x_436_; size_t v___x_437_; 
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_418_, v___x_436_);
v_i_418_ = v___x_437_;
v_b_419_ = v___x_435_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_415_ = stack[0].m_obj;
lean_object* v_as_416_ = stack[1].m_obj;
size_t v_sz_417_ = stack[2].m_num;
size_t v_i_418_ = stack[3].m_num;
lean_object* v_b_419_ = stack[4].m_obj;
lean_object* v___y_420_ = stack[5].m_obj;
lean_object* v___y_421_ = stack[6].m_obj;
lean_object* v___y_422_ = stack[7].m_obj;
lean_object* v___y_423_ = stack[8].m_obj;
lean_object* v_res_479_;
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_415_, v_as_416_, v_sz_417_, v_i_418_, v_b_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_e_480_, lean_object* v_as_481_, lean_object* v_sz_482_, lean_object* v_i_483_, lean_object* v_b_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
size_t v_sz_boxed_490_; size_t v_i_boxed_491_; lean_object* v_res_492_; 
v_sz_boxed_490_ = lean_unbox_usize(v_sz_482_);
lean_dec(v_sz_482_);
v_i_boxed_491_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_480_, v_as_481_, v_sz_boxed_490_, v_i_boxed_491_, v_b_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v_as_481_);
return v_res_492_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(lean_object* v_e_493_, lean_object* v_as_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_496_, v_sz_495_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_e_493_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_b_497_);
return v___x_509_;
}
else
{
lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_560_; 
v_snd_510_ = lean_ctor_get(v_b_497_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_b_497_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_b_497_, 0);
lean_dec(v_unused_561_);
v___x_512_ = v_b_497_;
v_isShared_513_ = v_isSharedCheck_560_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_dec(v_b_497_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_560_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v_a_516_; lean_object* v_a_523_; 
v___x_514_ = lean_box(0);
v_a_523_ = lean_array_uget(v_as_494_, v_i_496_);
if (lean_obj_tag(v_a_523_) == 0)
{
v_a_516_ = v_snd_510_;
goto v___jp_515_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_559_; 
v_val_524_ = lean_ctor_get(v_a_523_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_559_ == 0)
{
v___x_526_ = v_a_523_;
v_isShared_527_ = v_isSharedCheck_559_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v_a_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_559_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_528_ = lean_box(0);
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_530_ = l_Lean_LocalDecl_isAuxDecl(v_val_524_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Lean_LocalDecl_type(v_val_524_);
lean_inc_ref(v_e_493_);
v___x_532_ = l_Lean_Meta_isExprDefEq(v___x_531_, v_e_493_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_550_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_550_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_550_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_550_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint8_t v___x_537_; 
v___x_537_ = lean_unbox(v_a_533_);
lean_dec(v_a_533_);
if (v___x_537_ == 0)
{
lean_del_object(v___x_535_);
lean_del_object(v___x_526_);
lean_dec(v_val_524_);
lean_dec(v_snd_510_);
v_a_516_ = v___x_529_;
goto v___jp_515_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
lean_del_object(v___x_512_);
lean_dec_ref(v_e_493_);
v___x_538_ = l_Lean_LocalDecl_toExpr(v_val_524_);
v___x_539_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*1, v___x_508_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_539_);
v___x_541_ = v___x_526_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_549_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_528_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_snd_510_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_545_);
v___x_547_ = v___x_535_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_del_object(v___x_526_);
lean_dec(v_val_524_);
lean_del_object(v___x_512_);
lean_dec(v_snd_510_);
lean_dec_ref(v_e_493_);
v_a_551_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_532_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_532_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_del_object(v___x_526_);
lean_dec(v_val_524_);
lean_dec(v_snd_510_);
v_a_516_ = v___x_529_;
goto v___jp_515_;
}
}
}
v___jp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_a_516_);
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_a_516_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_496_, v___x_519_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_493_, v_as_494_, v_sz_495_, v___x_520_, v___x_518_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_493_ = stack[0].m_obj;
lean_object* v_as_494_ = stack[1].m_obj;
size_t v_sz_495_ = stack[2].m_num;
size_t v_i_496_ = stack[3].m_num;
lean_object* v_b_497_ = stack[4].m_obj;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v___y_500_ = stack[7].m_obj;
lean_object* v___y_501_ = stack[8].m_obj;
lean_object* v___y_502_ = stack[9].m_obj;
lean_object* v___y_503_ = stack[10].m_obj;
lean_object* v___y_504_ = stack[11].m_obj;
lean_object* v___y_505_ = stack[12].m_obj;
lean_object* v___y_506_ = stack[13].m_obj;
lean_object* v_res_562_;
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_493_, v_as_494_, v_sz_495_, v_i_496_, v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(lean_object* v_e_563_, lean_object* v_as_564_, lean_object* v_sz_565_, lean_object* v_i_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_565_);
lean_dec(v_sz_565_);
v_i_boxed_579_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_563_, v_as_564_, v_sz_boxed_578_, v_i_boxed_579_, v_b_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v_as_564_);
return v_res_580_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(lean_object* v_init_581_, lean_object* v_e_582_, lean_object* v_n_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
if (lean_obj_tag(v_n_583_) == 0)
{
lean_object* v_cs_595_; lean_object* v___x_596_; lean_object* v___x_597_; size_t v_sz_598_; size_t v___x_599_; lean_object* v___x_600_; 
v_cs_595_ = lean_ctor_get(v_n_583_, 0);
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v_b_584_);
v_sz_598_ = lean_array_size(v_cs_595_);
v___x_599_ = ((size_t)0ULL);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_581_, v_e_582_, v_cs_595_, v_sz_598_, v___x_599_, v___x_597_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_615_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_615_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_fst_605_; 
v_fst_605_ = lean_ctor_get(v_a_601_, 0);
if (lean_obj_tag(v_fst_605_) == 0)
{
lean_object* v_snd_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v_snd_606_ = lean_ctor_get(v_a_601_, 1);
lean_inc(v_snd_606_);
lean_dec(v_a_601_);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v_snd_606_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_607_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v_val_611_; lean_object* v___x_613_; 
lean_inc_ref(v_fst_605_);
lean_dec(v_a_601_);
v_val_611_ = lean_ctor_get(v_fst_605_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v_fst_605_, 1);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_val_611_);
v___x_613_ = v___x_603_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_val_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_600_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_600_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_vs_624_; lean_object* v___x_625_; lean_object* v___x_626_; size_t v_sz_627_; size_t v___x_628_; lean_object* v___x_629_; 
v_vs_624_ = lean_ctor_get(v_n_583_, 0);
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_b_584_);
v_sz_627_ = lean_array_size(v_vs_624_);
v___x_628_ = ((size_t)0ULL);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_582_, v_vs_624_, v_sz_627_, v___x_628_, v___x_626_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_644_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_644_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_644_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_644_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_fst_634_; 
v_fst_634_ = lean_ctor_get(v_a_630_, 0);
if (lean_obj_tag(v_fst_634_) == 0)
{
lean_object* v_snd_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v_snd_635_ = lean_ctor_get(v_a_630_, 1);
lean_inc(v_snd_635_);
lean_dec(v_a_630_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v_snd_635_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_636_);
v___x_638_ = v___x_632_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v_val_640_; lean_object* v___x_642_; 
lean_inc_ref(v_fst_634_);
lean_dec(v_a_630_);
v_val_640_ = lean_ctor_get(v_fst_634_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v_fst_634_, 1);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v_val_640_);
v___x_642_ = v___x_632_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_val_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_629_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_629_);
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
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_581_ = stack[0].m_obj;
lean_object* v_e_582_ = stack[1].m_obj;
lean_object* v_n_583_ = stack[2].m_obj;
lean_object* v_b_584_ = stack[3].m_obj;
lean_object* v___y_585_ = stack[4].m_obj;
lean_object* v___y_586_ = stack[5].m_obj;
lean_object* v___y_587_ = stack[6].m_obj;
lean_object* v___y_588_ = stack[7].m_obj;
lean_object* v___y_589_ = stack[8].m_obj;
lean_object* v___y_590_ = stack[9].m_obj;
lean_object* v___y_591_ = stack[10].m_obj;
lean_object* v___y_592_ = stack[11].m_obj;
lean_object* v___y_593_ = stack[12].m_obj;
lean_object* v_res_653_;
v_res_653_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_581_, v_e_582_, v_n_583_, v_b_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_653_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(lean_object* v_init_654_, lean_object* v_e_655_, lean_object* v_as_656_, size_t v_sz_657_, size_t v_i_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v_e_655_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_b_659_);
return v___x_671_;
}
else
{
lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_706_; 
v_snd_672_ = lean_ctor_get(v_b_659_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_b_659_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_b_659_, 0);
lean_dec(v_unused_707_);
v___x_674_ = v_b_659_;
v_isShared_675_ = v_isSharedCheck_706_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_dec(v_b_659_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_706_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v_a_677_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
v_a_677_ = lean_array_uget_borrowed(v_as_656_, v_i_658_);
lean_inc(v_snd_672_);
lean_inc_ref(v_e_655_);
v___x_678_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_654_, v_e_655_, v_a_677_, v_snd_672_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_697_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_697_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
if (lean_obj_tag(v_a_679_) == 0)
{
lean_object* v___x_683_; lean_object* v___x_685_; 
lean_dec_ref(v_e_655_);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_a_679_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_683_);
v___x_685_ = v___x_674_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_672_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_685_);
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; 
lean_del_object(v___x_681_);
lean_dec(v_snd_672_);
v_a_690_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v_a_679_, 1);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_a_690_);
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_692_ = v___x_674_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_690_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
size_t v___x_693_; size_t v___x_694_; 
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_add(v_i_658_, v___x_693_);
v_i_658_ = v___x_694_;
v_b_659_ = v___x_692_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_del_object(v___x_674_);
lean_dec(v_snd_672_);
lean_dec_ref(v_e_655_);
v_a_698_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_678_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_678_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_654_ = stack[0].m_obj;
lean_object* v_e_655_ = stack[1].m_obj;
lean_object* v_as_656_ = stack[2].m_obj;
size_t v_sz_657_ = stack[3].m_num;
size_t v_i_658_ = stack[4].m_num;
lean_object* v_b_659_ = stack[5].m_obj;
lean_object* v___y_660_ = stack[6].m_obj;
lean_object* v___y_661_ = stack[7].m_obj;
lean_object* v___y_662_ = stack[8].m_obj;
lean_object* v___y_663_ = stack[9].m_obj;
lean_object* v___y_664_ = stack[10].m_obj;
lean_object* v___y_665_ = stack[11].m_obj;
lean_object* v___y_666_ = stack[12].m_obj;
lean_object* v___y_667_ = stack[13].m_obj;
lean_object* v___y_668_ = stack[14].m_obj;
lean_object* v_res_708_;
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_654_, v_e_655_, v_as_656_, v_sz_657_, v_i_658_, v_b_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(lean_object* v_init_709_, lean_object* v_e_710_, lean_object* v_as_711_, lean_object* v_sz_712_, lean_object* v_i_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
size_t v_sz_boxed_725_; size_t v_i_boxed_726_; lean_object* v_res_727_; 
v_sz_boxed_725_ = lean_unbox_usize(v_sz_712_);
lean_dec(v_sz_712_);
v_i_boxed_726_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_709_, v_e_710_, v_as_711_, v_sz_boxed_725_, v_i_boxed_726_, v_b_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v_as_711_);
lean_dec_ref(v_init_709_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(lean_object* v_init_728_, lean_object* v_e_729_, lean_object* v_n_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_728_, v_e_729_, v_n_730_, v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v_n_730_);
lean_dec_ref(v_init_728_);
return v_res_742_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(lean_object* v_e_743_, lean_object* v_t_744_, lean_object* v_init_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_root_756_; lean_object* v_tail_757_; lean_object* v___x_758_; 
v_root_756_ = lean_ctor_get(v_t_744_, 0);
v_tail_757_ = lean_ctor_get(v_t_744_, 1);
lean_inc_ref(v_e_743_);
lean_inc_ref(v_init_745_);
v___x_758_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_745_, v_e_743_, v_root_756_, v_init_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_init_745_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_795_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_795_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_795_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_795_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
if (lean_obj_tag(v_a_759_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; 
lean_dec_ref(v_e_743_);
v_a_763_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v_a_759_, 1);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_a_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; size_t v_sz_770_; size_t v___x_771_; lean_object* v___x_772_; 
lean_del_object(v___x_761_);
v_a_767_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v_a_759_, 1);
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_a_767_);
v_sz_770_ = lean_array_size(v_tail_757_);
v___x_771_ = ((size_t)0ULL);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_743_, v_tail_757_, v_sz_770_, v___x_771_, v___x_769_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_786_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_786_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_fst_777_; 
v_fst_777_ = lean_ctor_get(v_a_773_, 0);
if (lean_obj_tag(v_fst_777_) == 0)
{
lean_object* v_snd_778_; lean_object* v___x_780_; 
v_snd_778_ = lean_ctor_get(v_a_773_, 1);
lean_inc(v_snd_778_);
lean_dec(v_a_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_snd_778_);
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_snd_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v_val_782_; lean_object* v___x_784_; 
lean_inc_ref(v_fst_777_);
lean_dec(v_a_773_);
v_val_782_ = lean_ctor_get(v_fst_777_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v_fst_777_, 1);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_val_782_);
v___x_784_ = v___x_775_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_val_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_772_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_772_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_e_743_);
v_a_796_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_758_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_758_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_743_ = stack[0].m_obj;
lean_object* v_t_744_ = stack[1].m_obj;
lean_object* v_init_745_ = stack[2].m_obj;
lean_object* v___y_746_ = stack[3].m_obj;
lean_object* v___y_747_ = stack[4].m_obj;
lean_object* v___y_748_ = stack[5].m_obj;
lean_object* v___y_749_ = stack[6].m_obj;
lean_object* v___y_750_ = stack[7].m_obj;
lean_object* v___y_751_ = stack[8].m_obj;
lean_object* v___y_752_ = stack[9].m_obj;
lean_object* v___y_753_ = stack[10].m_obj;
lean_object* v___y_754_ = stack[11].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_743_, v_t_744_, v_init_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(lean_object* v_e_805_, lean_object* v_t_806_, lean_object* v_init_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_805_, v_t_806_, v_init_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v_t_806_);
return v_res_818_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption(lean_object* v_e_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_lctx_835_; lean_object* v_decls_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_lctx_835_ = lean_ctor_get(v_a_830_, 2);
v_decls_836_ = lean_ctor_get(v_lctx_835_, 1);
v___x_837_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0));
v___x_838_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_824_, v_decls_836_, v___x_837_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_852_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_852_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_852_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_852_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_fst_843_; 
v_fst_843_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_fst_843_);
lean_dec(v_a_839_);
if (lean_obj_tag(v_fst_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1));
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v_val_848_; lean_object* v___x_850_; 
v_val_848_ = lean_ctor_get(v_fst_843_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_fst_843_, 1);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v_val_848_);
v___x_850_ = v___x_841_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_val_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_838_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_838_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_dischargeAssumption_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_824_ = stack[0].m_obj;
lean_object* v_a_825_ = stack[1].m_obj;
lean_object* v_a_826_ = stack[2].m_obj;
lean_object* v_a_827_ = stack[3].m_obj;
lean_object* v_a_828_ = stack[4].m_obj;
lean_object* v_a_829_ = stack[5].m_obj;
lean_object* v_a_830_ = stack[6].m_obj;
lean_object* v_a_831_ = stack[7].m_obj;
lean_object* v_a_832_ = stack[8].m_obj;
lean_object* v_a_833_ = stack[9].m_obj;
lean_object* v_res_861_;
v_res_861_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(v_e_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
stack->m_obj
 = v_res_861_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(lean_object* v_e_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(v_e_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
return v_res_873_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(lean_object* v_e_874_, lean_object* v_as_875_, size_t v_sz_876_, size_t v_i_877_, lean_object* v_b_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_874_, v_as_875_, v_sz_876_, v_i_877_, v_b_878_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_889_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_874_ = stack[0].m_obj;
lean_object* v_as_875_ = stack[1].m_obj;
size_t v_sz_876_ = stack[2].m_num;
size_t v_i_877_ = stack[3].m_num;
lean_object* v_b_878_ = stack[4].m_obj;
lean_object* v___y_879_ = stack[5].m_obj;
lean_object* v___y_880_ = stack[6].m_obj;
lean_object* v___y_881_ = stack[7].m_obj;
lean_object* v___y_882_ = stack[8].m_obj;
lean_object* v___y_883_ = stack[9].m_obj;
lean_object* v___y_884_ = stack[10].m_obj;
lean_object* v___y_885_ = stack[11].m_obj;
lean_object* v___y_886_ = stack[12].m_obj;
lean_object* v___y_887_ = stack[13].m_obj;
lean_object* v_res_890_;
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_874_, v_as_875_, v_sz_876_, v_i_877_, v_b_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(lean_object* v_e_891_, lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v_sz_boxed_906_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_907_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_891_, v_as_892_, v_sz_boxed_906_, v_i_boxed_907_, v_b_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v_as_892_);
return v_res_908_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(lean_object* v_e_909_, lean_object* v_as_910_, size_t v_sz_911_, size_t v_i_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_909_, v_as_910_, v_sz_911_, v_i_912_, v_b_913_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_909_ = stack[0].m_obj;
lean_object* v_as_910_ = stack[1].m_obj;
size_t v_sz_911_ = stack[2].m_num;
size_t v_i_912_ = stack[3].m_num;
lean_object* v_b_913_ = stack[4].m_obj;
lean_object* v___y_914_ = stack[5].m_obj;
lean_object* v___y_915_ = stack[6].m_obj;
lean_object* v___y_916_ = stack[7].m_obj;
lean_object* v___y_917_ = stack[8].m_obj;
lean_object* v___y_918_ = stack[9].m_obj;
lean_object* v___y_919_ = stack[10].m_obj;
lean_object* v___y_920_ = stack[11].m_obj;
lean_object* v___y_921_ = stack[12].m_obj;
lean_object* v___y_922_ = stack[13].m_obj;
lean_object* v_res_925_;
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_909_, v_as_910_, v_sz_911_, v_i_912_, v_b_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_e_926_, lean_object* v_as_927_, lean_object* v_sz_928_, lean_object* v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_928_);
lean_dec(v_sz_928_);
v_i_boxed_942_ = lean_unbox_usize(v_i_929_);
lean_dec(v_i_929_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_926_, v_as_927_, v_sz_boxed_941_, v_i_boxed_942_, v_b_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v_as_927_);
return v_res_943_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
}
#ifdef __cplusplus
}
#endif
