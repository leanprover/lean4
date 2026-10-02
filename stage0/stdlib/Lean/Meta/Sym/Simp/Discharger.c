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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
uint8_t v_contextDependent_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_contextDependent_8_ = lean_ctor_get_uint8(v_t_6_, 0);
lean_dec_ref_known(v_t_6_, 0);
v___x_9_ = lean_box(v_contextDependent_8_);
v___x_10_ = lean_apply_1(v_k_7_, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_proof_11_; uint8_t v_contextDependent_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_proof_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_proof_11_);
v_contextDependent_12_ = lean_ctor_get_uint8(v_t_6_, sizeof(void*)*1);
lean_dec_ref_known(v_t_6_, 1);
v___x_13_ = lean_box(v_contextDependent_12_);
v___x_14_ = lean_apply_2(v_k_7_, v_proof_11_, v___x_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(lean_object* v_t_27_, lean_object* v_failed_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_27_, v_failed_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_failed_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_31_, v_failed_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(lean_object* v_t_35_, lean_object* v_solved_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_35_, v_solved_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_solved_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_39_, v_solved_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(lean_object* v_e_43_, lean_object* v_result_44_){
_start:
{
if (lean_obj_tag(v_result_44_) == 0)
{
uint8_t v_contextDependent_45_; lean_object* v___x_46_; 
lean_dec_ref(v_e_43_);
v_contextDependent_45_ = lean_ctor_get_uint8(v_result_44_, 1);
lean_dec_ref_known(v_result_44_, 0);
v___x_46_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_46_, 0, v_contextDependent_45_);
return v___x_46_;
}
else
{
lean_object* v_e_x27_47_; lean_object* v_proof_48_; uint8_t v_contextDependent_49_; uint8_t v___x_50_; 
v_e_x27_47_ = lean_ctor_get(v_result_44_, 0);
lean_inc_ref(v_e_x27_47_);
v_proof_48_ = lean_ctor_get(v_result_44_, 1);
lean_inc_ref(v_proof_48_);
v_contextDependent_49_ = lean_ctor_get_uint8(v_result_44_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_result_44_, 2);
v___x_50_ = l_Lean_Expr_isTrue(v_e_x27_47_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec_ref(v_proof_48_);
lean_dec_ref(v_e_43_);
v___x_51_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_51_, 0, v_contextDependent_49_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Lean_Meta_mkOfEqTrueCore(v_e_43_, v_proof_48_);
v___x_53_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*1, v_contextDependent_49_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(lean_object* v_p_54_, lean_object* v_e_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
lean_inc(v_a_60_);
lean_inc_ref(v_a_59_);
lean_inc(v_a_58_);
lean_inc_ref(v_a_57_);
lean_inc(v_a_56_);
lean_inc_ref(v_e_55_);
v___x_66_ = lean_apply_11(v_p_54_, v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, lean_box(0));
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_55_, v_a_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec_ref(v_e_55_);
v_a_76_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_66_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_66_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(lean_object* v_a_97_, lean_object* v_persistentCache_98_, lean_object* v_transientCache_99_, lean_object* v_funext_100_, lean_object* v_a_x3f_101_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(lean_object* v_a_118_, lean_object* v_persistentCache_119_, lean_object* v_transientCache_120_, lean_object* v_funext_121_, lean_object* v_a_x3f_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_118_, v_persistentCache_119_, v_transientCache_120_, v_funext_121_, v_a_x3f_122_);
lean_dec(v_a_x3f_122_);
lean_dec(v_a_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_129_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_191_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_191_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_191_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_191_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_maxDischargeDepth_143_; lean_object* v_config_144_; lean_object* v_initialLCtxSize_145_; lean_object* v_dischargeDepth_146_; uint8_t v___x_147_; 
v_maxDischargeDepth_143_ = lean_ctor_get(v_a_139_, 1);
lean_inc(v_maxDischargeDepth_143_);
lean_dec(v_a_139_);
v_config_144_ = lean_ctor_get(v_a_129_, 0);
v_initialLCtxSize_145_ = lean_ctor_get(v_a_129_, 1);
v_dischargeDepth_146_ = lean_ctor_get(v_a_129_, 2);
v___x_147_ = lean_nat_dec_lt(v_maxDischargeDepth_143_, v_dischargeDepth_146_);
lean_dec(v_maxDischargeDepth_143_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_persistentCache_149_; lean_object* v___x_150_; lean_object* v_transientCache_151_; lean_object* v___x_152_; lean_object* v_funext_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_del_object(v___x_141_);
v___x_148_ = lean_st_ref_get(v_a_130_);
v_persistentCache_149_ = lean_ctor_get(v___x_148_, 1);
lean_inc_ref(v_persistentCache_149_);
lean_dec(v___x_148_);
v___x_150_ = lean_st_ref_get(v_a_130_);
v_transientCache_151_ = lean_ctor_get(v___x_150_, 2);
lean_inc_ref(v_transientCache_151_);
lean_dec(v___x_150_);
v___x_152_ = lean_st_ref_get(v_a_130_);
v_funext_153_ = lean_ctor_get(v___x_152_, 3);
lean_inc_ref(v_funext_153_);
lean_dec(v___x_152_);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_dischargeDepth_146_, v___x_154_);
lean_inc(v_initialLCtxSize_145_);
lean_inc_ref(v_config_144_);
v___x_156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_156_, 0, v_config_144_);
lean_ctor_set(v___x_156_, 1, v_initialLCtxSize_145_);
lean_ctor_set(v___x_156_, 2, v___x_155_);
lean_inc(v_a_136_);
lean_inc_ref(v_a_135_);
lean_inc(v_a_134_);
lean_inc_ref(v_a_133_);
lean_inc(v_a_132_);
lean_inc_ref(v_a_131_);
lean_inc(v_a_130_);
lean_inc(v_a_128_);
lean_inc_ref(v_e_127_);
v___x_157_ = lean_sym_simp(v_e_127_, v_a_128_, v___x_156_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_175_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_175_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_175_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_175_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_127_, v_a_158_);
lean_inc_ref(v___x_162_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_174_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v___x_165_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_130_, v_persistentCache_149_, v_transientCache_151_, v_funext_153_, v___x_164_);
lean_dec_ref(v___x_164_);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v___x_165_, 0);
lean_dec(v_unused_173_);
v___x_167_ = v___x_165_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_dec(v___x_165_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_162_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_162_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v_e_127_);
v_a_176_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_157_, 1);
v___x_177_ = lean_box(0);
v___x_178_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_130_, v_persistentCache_149_, v_transientCache_151_, v_funext_153_, v___x_177_);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_186_);
v___x_180_ = v___x_178_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_dec(v___x_178_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 1);
lean_ctor_set(v___x_180_, 0, v_a_176_);
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_176_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_dec_ref(v_e_127_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0));
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_187_);
v___x_189_ = v___x_141_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_e_127_);
v_a_192_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_138_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_138_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object* v_e_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf(v_e_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg(){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0));
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone(lean_object* v_x_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object* v_x_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Sym_Simp_dischargeNone(v_x_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_x_229_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(lean_object* v_e_244_, lean_object* v_as_245_, size_t v_sz_246_, size_t v_i_247_, lean_object* v_b_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_usize_dec_lt(v_i_247_, v_sz_246_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec_ref(v_e_244_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_b_248_);
return v___x_255_;
}
else
{
lean_object* v_snd_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_305_; 
v_snd_256_ = lean_ctor_get(v_b_248_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_b_248_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_b_248_, 0);
lean_dec(v_unused_306_);
v___x_258_ = v_b_248_;
v_isShared_259_ = v_isSharedCheck_305_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snd_256_);
lean_dec(v_b_248_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_305_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v_a_262_; lean_object* v_a_269_; 
v___x_260_ = lean_box(0);
v_a_269_ = lean_array_uget(v_as_245_, v_i_247_);
if (lean_obj_tag(v_a_269_) == 0)
{
v_a_262_ = v_snd_256_;
goto v___jp_261_;
}
else
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_304_; 
v_val_270_ = lean_ctor_get(v_a_269_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_a_269_);
if (v_isSharedCheck_304_ == 0)
{
v___x_272_ = v_a_269_;
v_isShared_273_ = v_isSharedCheck_304_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v_a_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_304_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_276_ = l_Lean_LocalDecl_isAuxDecl(v_val_270_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_Lean_LocalDecl_type(v_val_270_);
lean_inc_ref(v_e_244_);
v___x_278_ = l_Lean_Meta_isExprDefEq(v___x_277_, v_e_244_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_295_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_295_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_295_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = lean_unbox(v_a_279_);
lean_dec(v_a_279_);
if (v___x_283_ == 0)
{
lean_del_object(v___x_281_);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_snd_256_);
v_a_262_ = v___x_275_;
goto v___jp_261_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_del_object(v___x_258_);
lean_dec_ref(v_e_244_);
v___x_284_ = l_Lean_LocalDecl_toExpr(v_val_270_);
v___x_285_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1, v___x_254_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_285_);
v___x_287_ = v___x_272_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_294_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_274_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_snd_256_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_290_);
v___x_292_ = v___x_281_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_del_object(v___x_258_);
lean_dec(v_snd_256_);
lean_dec_ref(v_e_244_);
v_a_296_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_278_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_278_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_snd_256_);
v_a_262_ = v___x_275_;
goto v___jp_261_;
}
}
}
v___jp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v_a_262_);
lean_ctor_set(v___x_258_, 0, v___x_260_);
v___x_264_ = v___x_258_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_a_262_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
size_t v___x_265_; size_t v___x_266_; 
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_247_, v___x_265_);
v_i_247_ = v___x_266_;
v_b_248_ = v___x_264_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_e_307_, lean_object* v_as_308_, lean_object* v_sz_309_, lean_object* v_i_310_, lean_object* v_b_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
size_t v_sz_boxed_317_; size_t v_i_boxed_318_; lean_object* v_res_319_; 
v_sz_boxed_317_ = lean_unbox_usize(v_sz_309_);
lean_dec(v_sz_309_);
v_i_boxed_318_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_307_, v_as_308_, v_sz_boxed_317_, v_i_boxed_318_, v_b_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v_as_308_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(lean_object* v_e_320_, lean_object* v_as_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v_e_320_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_b_324_);
return v___x_336_;
}
else
{
lean_object* v_snd_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_386_; 
v_snd_337_ = lean_ctor_get(v_b_324_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_b_324_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v_b_324_, 0);
lean_dec(v_unused_387_);
v___x_339_ = v_b_324_;
v_isShared_340_ = v_isSharedCheck_386_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snd_337_);
lean_dec(v_b_324_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_386_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v_a_343_; lean_object* v_a_350_; 
v___x_341_ = lean_box(0);
v_a_350_ = lean_array_uget(v_as_321_, v_i_323_);
if (lean_obj_tag(v_a_350_) == 0)
{
v_a_343_ = v_snd_337_;
goto v___jp_342_;
}
else
{
lean_object* v_val_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_385_; 
v_val_351_ = lean_ctor_get(v_a_350_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_a_350_);
if (v_isSharedCheck_385_ == 0)
{
v___x_353_ = v_a_350_;
v_isShared_354_ = v_isSharedCheck_385_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_val_351_);
lean_dec(v_a_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_385_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = lean_box(0);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_357_ = l_Lean_LocalDecl_isAuxDecl(v_val_351_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_LocalDecl_type(v_val_351_);
lean_inc_ref(v_e_320_);
v___x_359_ = l_Lean_Meta_isExprDefEq(v___x_358_, v_e_320_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_376_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_376_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
uint8_t v___x_364_; 
v___x_364_ = lean_unbox(v_a_360_);
lean_dec(v_a_360_);
if (v___x_364_ == 0)
{
lean_del_object(v___x_362_);
lean_del_object(v___x_353_);
lean_dec(v_val_351_);
lean_dec(v_snd_337_);
v_a_343_ = v___x_356_;
goto v___jp_342_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
lean_del_object(v___x_339_);
lean_dec_ref(v_e_320_);
v___x_365_ = l_Lean_LocalDecl_toExpr(v_val_351_);
v___x_366_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_335_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_366_);
v___x_368_ = v___x_353_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_375_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_355_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v_snd_337_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_371_);
v___x_373_ = v___x_362_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_del_object(v___x_353_);
lean_dec(v_val_351_);
lean_del_object(v___x_339_);
lean_dec(v_snd_337_);
lean_dec_ref(v_e_320_);
v_a_377_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_359_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_359_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_del_object(v___x_353_);
lean_dec(v_val_351_);
lean_dec(v_snd_337_);
v_a_343_ = v___x_356_;
goto v___jp_342_;
}
}
}
v___jp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_a_343_);
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_345_ = v___x_339_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_a_343_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_323_, v___x_346_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_320_, v_as_321_, v_sz_322_, v___x_347_, v___x_345_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
return v___x_348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(lean_object* v_e_388_, lean_object* v_as_389_, lean_object* v_sz_390_, lean_object* v_i_391_, lean_object* v_b_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
size_t v_sz_boxed_403_; size_t v_i_boxed_404_; lean_object* v_res_405_; 
v_sz_boxed_403_ = lean_unbox_usize(v_sz_390_);
lean_dec(v_sz_390_);
v_i_boxed_404_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_388_, v_as_389_, v_sz_boxed_403_, v_i_boxed_404_, v_b_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v_as_389_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_e_409_, lean_object* v_as_410_, size_t v_sz_411_, size_t v_i_412_, lean_object* v_b_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = lean_usize_dec_lt(v_i_412_, v_sz_411_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v_e_409_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_b_413_);
return v___x_420_;
}
else
{
lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_471_; 
v_snd_421_ = lean_ctor_get(v_b_413_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_b_413_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_b_413_, 0);
lean_dec(v_unused_472_);
v___x_423_ = v_b_413_;
v_isShared_424_ = v_isSharedCheck_471_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_dec(v_b_413_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_471_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v_a_427_; lean_object* v_a_434_; 
v___x_425_ = lean_box(0);
v_a_434_ = lean_array_uget(v_as_410_, v_i_412_);
if (lean_obj_tag(v_a_434_) == 0)
{
v_a_427_ = v_snd_421_;
goto v___jp_426_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_470_; 
v_val_435_ = lean_ctor_get(v_a_434_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_470_ == 0)
{
v___x_437_ = v_a_434_;
v_isShared_438_ = v_isSharedCheck_470_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v_a_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_470_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_box(0);
v___x_440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_441_ = l_Lean_LocalDecl_isAuxDecl(v_val_435_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = l_Lean_LocalDecl_type(v_val_435_);
lean_inc_ref(v_e_409_);
v___x_443_ = l_Lean_Meta_isExprDefEq(v___x_442_, v_e_409_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_461_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_461_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_461_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_461_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; 
v___x_448_ = lean_unbox(v_a_444_);
lean_dec(v_a_444_);
if (v___x_448_ == 0)
{
lean_del_object(v___x_446_);
lean_del_object(v___x_437_);
lean_dec(v_val_435_);
lean_dec(v_snd_421_);
v_a_427_ = v___x_440_;
goto v___jp_426_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
lean_del_object(v___x_423_);
lean_dec_ref(v_e_409_);
v___x_449_ = l_Lean_LocalDecl_toExpr(v_val_435_);
v___x_450_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_419_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_450_);
v___x_452_ = v___x_437_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_460_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_439_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_snd_421_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_456_);
v___x_458_ = v___x_446_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_del_object(v___x_437_);
lean_dec(v_val_435_);
lean_del_object(v___x_423_);
lean_dec(v_snd_421_);
lean_dec_ref(v_e_409_);
v_a_462_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_443_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_443_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_del_object(v___x_437_);
lean_dec(v_val_435_);
lean_dec(v_snd_421_);
v_a_427_ = v___x_440_;
goto v___jp_426_;
}
}
}
v___jp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_a_427_);
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_427_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
size_t v___x_430_; size_t v___x_431_; 
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_412_, v___x_430_);
v_i_412_ = v___x_431_;
v_b_413_ = v___x_429_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_e_473_, lean_object* v_as_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
size_t v_sz_boxed_483_; size_t v_i_boxed_484_; lean_object* v_res_485_; 
v_sz_boxed_483_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_484_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_473_, v_as_474_, v_sz_boxed_483_, v_i_boxed_484_, v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v_as_474_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(lean_object* v_e_486_, lean_object* v_as_487_, size_t v_sz_488_, size_t v_i_489_, lean_object* v_b_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_lt(v_i_489_, v_sz_488_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_e_486_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v_b_490_);
return v___x_502_;
}
else
{
lean_object* v_snd_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_553_; 
v_snd_503_ = lean_ctor_get(v_b_490_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_b_490_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_b_490_, 0);
lean_dec(v_unused_554_);
v___x_505_ = v_b_490_;
v_isShared_506_ = v_isSharedCheck_553_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snd_503_);
lean_dec(v_b_490_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_553_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v_a_509_; lean_object* v_a_516_; 
v___x_507_ = lean_box(0);
v_a_516_ = lean_array_uget(v_as_487_, v_i_489_);
if (lean_obj_tag(v_a_516_) == 0)
{
v_a_509_ = v_snd_503_;
goto v___jp_508_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_552_; 
v_val_517_ = lean_ctor_get(v_a_516_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_516_);
if (v_isSharedCheck_552_ == 0)
{
v___x_519_ = v_a_516_;
v_isShared_520_ = v_isSharedCheck_552_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v_a_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_552_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_box(0);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_523_ = l_Lean_LocalDecl_isAuxDecl(v_val_517_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_LocalDecl_type(v_val_517_);
lean_inc_ref(v_e_486_);
v___x_525_ = l_Lean_Meta_isExprDefEq(v___x_524_, v_e_486_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_543_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_543_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_543_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_543_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint8_t v___x_530_; 
v___x_530_ = lean_unbox(v_a_526_);
lean_dec(v_a_526_);
if (v___x_530_ == 0)
{
lean_del_object(v___x_528_);
lean_del_object(v___x_519_);
lean_dec(v_val_517_);
lean_dec(v_snd_503_);
v_a_509_ = v___x_522_;
goto v___jp_508_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_del_object(v___x_505_);
lean_dec_ref(v_e_486_);
v___x_531_ = l_Lean_LocalDecl_toExpr(v_val_517_);
v___x_532_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_501_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_532_);
v___x_534_ = v___x_519_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_542_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_521_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_snd_503_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_538_);
v___x_540_ = v___x_528_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_519_);
lean_dec(v_val_517_);
lean_del_object(v___x_505_);
lean_dec(v_snd_503_);
lean_dec_ref(v_e_486_);
v_a_544_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_525_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_525_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_del_object(v___x_519_);
lean_dec(v_val_517_);
lean_dec(v_snd_503_);
v_a_509_ = v___x_522_;
goto v___jp_508_;
}
}
}
v___jp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_a_509_);
lean_ctor_set(v___x_505_, 0, v___x_507_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_a_509_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_489_, v___x_512_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_486_, v_as_487_, v_sz_488_, v___x_513_, v___x_511_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(lean_object* v_e_555_, lean_object* v_as_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_b_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
size_t v_sz_boxed_570_; size_t v_i_boxed_571_; lean_object* v_res_572_; 
v_sz_boxed_570_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_571_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_555_, v_as_556_, v_sz_boxed_570_, v_i_boxed_571_, v_b_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v_as_556_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(lean_object* v_init_573_, lean_object* v_e_574_, lean_object* v_n_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
if (lean_obj_tag(v_n_575_) == 0)
{
lean_object* v_cs_587_; lean_object* v___x_588_; lean_object* v___x_589_; size_t v_sz_590_; size_t v___x_591_; lean_object* v___x_592_; 
v_cs_587_ = lean_ctor_get(v_n_575_, 0);
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v_b_576_);
v_sz_590_ = lean_array_size(v_cs_587_);
v___x_591_ = ((size_t)0ULL);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_573_, v_e_574_, v_cs_587_, v_sz_590_, v___x_591_, v___x_589_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_607_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_607_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_fst_597_; 
v_fst_597_ = lean_ctor_get(v_a_593_, 0);
if (lean_obj_tag(v_fst_597_) == 0)
{
lean_object* v_snd_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v_snd_598_ = lean_ctor_get(v_a_593_, 1);
lean_inc(v_snd_598_);
lean_dec(v_a_593_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_snd_598_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_599_);
v___x_601_ = v___x_595_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
else
{
lean_object* v_val_603_; lean_object* v___x_605_; 
lean_inc_ref(v_fst_597_);
lean_dec(v_a_593_);
v_val_603_ = lean_ctor_get(v_fst_597_, 0);
lean_inc(v_val_603_);
lean_dec_ref_known(v_fst_597_, 1);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_val_603_);
v___x_605_ = v___x_595_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_val_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_592_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_592_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
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
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
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
lean_object* v_vs_616_; lean_object* v___x_617_; lean_object* v___x_618_; size_t v_sz_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_vs_616_ = lean_ctor_get(v_n_575_, 0);
v___x_617_ = lean_box(0);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v_b_576_);
v_sz_619_ = lean_array_size(v_vs_616_);
v___x_620_ = ((size_t)0ULL);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_574_, v_vs_616_, v_sz_619_, v___x_620_, v___x_618_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_636_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_636_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_636_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_636_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_fst_626_; 
v_fst_626_ = lean_ctor_get(v_a_622_, 0);
if (lean_obj_tag(v_fst_626_) == 0)
{
lean_object* v_snd_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v_snd_627_ = lean_ctor_get(v_a_622_, 1);
lean_inc(v_snd_627_);
lean_dec(v_a_622_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v_snd_627_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_628_);
v___x_630_ = v___x_624_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v_val_632_; lean_object* v___x_634_; 
lean_inc_ref(v_fst_626_);
lean_dec(v_a_622_);
v_val_632_ = lean_ctor_get(v_fst_626_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_fst_626_, 1);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v_val_632_);
v___x_634_ = v___x_624_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_val_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_a_637_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_621_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_621_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(lean_object* v_init_645_, lean_object* v_e_646_, lean_object* v_as_647_, size_t v_sz_648_, size_t v_i_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_e_646_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_b_650_);
return v___x_662_;
}
else
{
lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_697_; 
v_snd_663_ = lean_ctor_get(v_b_650_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_b_650_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_b_650_, 0);
lean_dec(v_unused_698_);
v___x_665_ = v_b_650_;
v_isShared_666_ = v_isSharedCheck_697_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_dec(v_b_650_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_697_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
v_a_668_ = lean_array_uget_borrowed(v_as_647_, v_i_649_);
lean_inc(v_snd_663_);
lean_inc_ref(v_e_646_);
v___x_669_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_645_, v_e_646_, v_a_668_, v_snd_663_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_688_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_688_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_688_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_688_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
if (lean_obj_tag(v_a_670_) == 0)
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_dec_ref(v_e_646_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_a_670_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_674_);
v___x_676_ = v___x_665_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_snd_663_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_676_);
v___x_678_ = v___x_672_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; 
lean_del_object(v___x_672_);
lean_dec(v_snd_663_);
v_a_681_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v_a_670_, 1);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_a_681_);
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_683_ = v___x_665_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_681_);
v___x_683_ = v_reuseFailAlloc_687_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
size_t v___x_684_; size_t v___x_685_; 
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_add(v_i_649_, v___x_684_);
v_i_649_ = v___x_685_;
v_b_650_ = v___x_683_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_del_object(v___x_665_);
lean_dec(v_snd_663_);
lean_dec_ref(v_e_646_);
v_a_689_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_669_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_669_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(lean_object* v_init_699_, lean_object* v_e_700_, lean_object* v_as_701_, lean_object* v_sz_702_, lean_object* v_i_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_702_);
lean_dec(v_sz_702_);
v_i_boxed_716_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_699_, v_e_700_, v_as_701_, v_sz_boxed_715_, v_i_boxed_716_, v_b_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v_as_701_);
lean_dec_ref(v_init_699_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(lean_object* v_init_718_, lean_object* v_e_719_, lean_object* v_n_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_718_, v_e_719_, v_n_720_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v_n_720_);
lean_dec_ref(v_init_718_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(lean_object* v_e_733_, lean_object* v_t_734_, lean_object* v_init_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_root_746_; lean_object* v_tail_747_; lean_object* v___x_748_; 
v_root_746_ = lean_ctor_get(v_t_734_, 0);
v_tail_747_ = lean_ctor_get(v_t_734_, 1);
lean_inc_ref(v_e_733_);
lean_inc_ref(v_init_735_);
v___x_748_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_735_, v_e_733_, v_root_746_, v_init_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_init_735_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_785_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_785_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_785_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_785_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
if (lean_obj_tag(v_a_749_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; 
lean_dec_ref(v_e_733_);
v_a_753_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v_a_749_, 1);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v_a_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; size_t v_sz_760_; size_t v___x_761_; lean_object* v___x_762_; 
lean_del_object(v___x_751_);
v_a_757_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v_a_749_, 1);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v_a_757_);
v_sz_760_ = lean_array_size(v_tail_747_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_733_, v_tail_747_, v_sz_760_, v___x_761_, v___x_759_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_776_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_776_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_fst_767_; 
v_fst_767_ = lean_ctor_get(v_a_763_, 0);
if (lean_obj_tag(v_fst_767_) == 0)
{
lean_object* v_snd_768_; lean_object* v___x_770_; 
v_snd_768_ = lean_ctor_get(v_a_763_, 1);
lean_inc(v_snd_768_);
lean_dec(v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_snd_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_snd_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v_val_772_; lean_object* v___x_774_; 
lean_inc_ref(v_fst_767_);
lean_dec(v_a_763_);
v_val_772_ = lean_ctor_get(v_fst_767_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v_fst_767_, 1);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_val_772_);
v___x_774_ = v___x_765_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_val_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_777_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_762_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_762_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_e_733_);
v_a_786_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_748_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_748_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(lean_object* v_e_794_, lean_object* v_t_795_, lean_object* v_init_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_794_, v_t_795_, v_init_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v_t_795_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption(lean_object* v_e_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_lctx_824_; lean_object* v_decls_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_lctx_824_ = lean_ctor_get(v_a_819_, 2);
v_decls_825_ = lean_ctor_get(v_lctx_824_, 1);
v___x_826_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0));
v___x_827_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_813_, v_decls_825_, v___x_826_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_841_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_841_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_fst_832_; 
v_fst_832_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_fst_832_);
lean_dec(v_a_828_);
if (lean_obj_tag(v_fst_832_) == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1));
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_val_837_; lean_object* v___x_839_; 
v_val_837_ = lean_ctor_get(v_fst_832_, 0);
lean_inc(v_val_837_);
lean_dec_ref_known(v_fst_832_, 1);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_val_837_);
v___x_839_ = v___x_830_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_val_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_827_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_827_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(lean_object* v_e_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(v_e_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(lean_object* v_e_862_, lean_object* v_as_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_862_, v_as_863_, v_sz_864_, v_i_865_, v_b_866_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(lean_object* v_e_878_, lean_object* v_as_879_, lean_object* v_sz_880_, lean_object* v_i_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
size_t v_sz_boxed_893_; size_t v_i_boxed_894_; lean_object* v_res_895_; 
v_sz_boxed_893_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v_i_boxed_894_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_res_895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_878_, v_as_879_, v_sz_boxed_893_, v_i_boxed_894_, v_b_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v_as_879_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(lean_object* v_e_896_, lean_object* v_as_897_, size_t v_sz_898_, size_t v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_896_, v_as_897_, v_sz_898_, v_i_899_, v_b_900_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_e_912_, lean_object* v_as_913_, lean_object* v_sz_914_, lean_object* v_i_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
size_t v_sz_boxed_927_; size_t v_i_boxed_928_; lean_object* v_res_929_; 
v_sz_boxed_927_ = lean_unbox_usize(v_sz_914_);
lean_dec(v_sz_914_);
v_i_boxed_928_ = lean_unbox_usize(v_i_915_);
lean_dec(v_i_915_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_912_, v_as_913_, v_sz_boxed_927_, v_i_boxed_928_, v_b_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v_as_913_);
return v_res_929_;
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
