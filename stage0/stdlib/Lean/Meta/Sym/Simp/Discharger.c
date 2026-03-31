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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_result_44_);
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
lean_dec_ref(v_result_44_);
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
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 3, v_funext_100_);
lean_ctor_set(v___x_106_, 2, v_transientCache_99_);
lean_ctor_set(v___x_106_, 1, v_persistentCache_98_);
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_numSteps_104_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_persistentCache_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_transientCache_99_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_funext_100_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_st_ref_set(v_a_97_, v___x_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
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
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_persistentCache_151_; lean_object* v_transientCache_152_; lean_object* v_funext_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_del_object(v___x_141_);
v___x_148_ = lean_st_ref_get(v_a_130_);
v___x_149_ = lean_st_ref_get(v_a_130_);
v___x_150_ = lean_st_ref_get(v_a_130_);
v_persistentCache_151_ = lean_ctor_get(v___x_148_, 1);
lean_inc_ref(v_persistentCache_151_);
lean_dec(v___x_148_);
v_transientCache_152_ = lean_ctor_get(v___x_149_, 2);
lean_inc_ref(v_transientCache_152_);
lean_dec(v___x_149_);
v_funext_153_ = lean_ctor_get(v___x_150_, 3);
lean_inc_ref(v_funext_153_);
lean_dec(v___x_150_);
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
v___x_165_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_130_, v_persistentCache_151_, v_transientCache_152_, v_funext_153_, v___x_164_);
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
lean_dec_ref(v___x_157_);
v___x_177_ = lean_box(0);
v___x_178_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_130_, v_persistentCache_151_, v_transientCache_152_, v_funext_153_, v___x_177_);
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
lean_object* v_snd_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_306_; 
v_snd_256_ = lean_ctor_get(v_b_248_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_b_248_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_b_248_, 0);
lean_dec(v_unused_307_);
v___x_258_ = v_b_248_;
v_isShared_259_ = v_isSharedCheck_306_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snd_256_);
lean_dec(v_b_248_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_306_;
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
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_305_; 
v_val_270_ = lean_ctor_get(v_a_269_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_a_269_);
if (v_isSharedCheck_305_ == 0)
{
v___x_272_ = v_a_269_;
v_isShared_273_ = v_isSharedCheck_305_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v_a_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_305_;
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
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_296_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_296_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_296_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_296_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = lean_unbox(v_a_279_);
if (v___x_283_ == 0)
{
lean_del_object(v___x_281_);
lean_dec(v_a_279_);
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_dec(v_snd_256_);
v_a_262_ = v___x_275_;
goto v___jp_261_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_288_; 
lean_del_object(v___x_258_);
lean_dec_ref(v_e_244_);
v___x_284_ = l_Lean_LocalDecl_toExpr(v_val_270_);
v___x_285_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = lean_unbox(v_a_279_);
lean_dec(v_a_279_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1, v___x_286_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_285_);
v___x_288_ = v___x_272_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_285_);
v___x_288_ = v_reuseFailAlloc_295_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_274_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_snd_256_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_291_);
v___x_293_ = v___x_281_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_del_object(v___x_272_);
lean_dec(v_val_270_);
lean_del_object(v___x_258_);
lean_dec(v_snd_256_);
lean_dec_ref(v_e_244_);
v_a_297_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_278_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_278_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_e_308_, lean_object* v_as_309_, lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_b_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
size_t v_sz_boxed_318_; size_t v_i_boxed_319_; lean_object* v_res_320_; 
v_sz_boxed_318_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_319_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_308_, v_as_309_, v_sz_boxed_318_, v_i_boxed_319_, v_b_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec_ref(v_as_309_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(lean_object* v_e_321_, lean_object* v_as_322_, size_t v_sz_323_, size_t v_i_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v_e_321_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v_b_325_);
return v___x_337_;
}
else
{
lean_object* v_snd_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_388_; 
v_snd_338_ = lean_ctor_get(v_b_325_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_b_325_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v_b_325_, 0);
lean_dec(v_unused_389_);
v___x_340_ = v_b_325_;
v_isShared_341_ = v_isSharedCheck_388_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snd_338_);
lean_dec(v_b_325_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_388_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v_a_344_; lean_object* v_a_351_; 
v___x_342_ = lean_box(0);
v_a_351_ = lean_array_uget(v_as_322_, v_i_324_);
if (lean_obj_tag(v_a_351_) == 0)
{
v_a_344_ = v_snd_338_;
goto v___jp_343_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_387_; 
v_val_352_ = lean_ctor_get(v_a_351_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_a_351_);
if (v_isSharedCheck_387_ == 0)
{
v___x_354_ = v_a_351_;
v_isShared_355_ = v_isSharedCheck_387_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_val_352_);
lean_dec(v_a_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_387_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_box(0);
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_358_ = l_Lean_LocalDecl_isAuxDecl(v_val_352_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Lean_LocalDecl_type(v_val_352_);
lean_inc_ref(v_e_321_);
v___x_360_ = l_Lean_Meta_isExprDefEq(v___x_359_, v_e_321_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_378_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_378_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_378_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_378_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
uint8_t v___x_365_; 
v___x_365_ = lean_unbox(v_a_361_);
if (v___x_365_ == 0)
{
lean_del_object(v___x_363_);
lean_dec(v_a_361_);
lean_del_object(v___x_354_);
lean_dec(v_val_352_);
lean_dec(v_snd_338_);
v_a_344_ = v___x_357_;
goto v___jp_343_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_370_; 
lean_del_object(v___x_340_);
lean_dec_ref(v_e_321_);
v___x_366_ = l_Lean_LocalDecl_toExpr(v_val_352_);
v___x_367_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_366_);
v___x_368_ = lean_unbox(v_a_361_);
lean_dec(v_a_361_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_368_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_367_);
v___x_370_ = v___x_354_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_367_);
v___x_370_ = v_reuseFailAlloc_377_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_356_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_snd_338_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_373_);
v___x_375_ = v___x_363_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_354_);
lean_dec(v_val_352_);
lean_del_object(v___x_340_);
lean_dec(v_snd_338_);
lean_dec_ref(v_e_321_);
v_a_379_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_360_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_360_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_del_object(v___x_354_);
lean_dec(v_val_352_);
lean_dec(v_snd_338_);
v_a_344_ = v___x_357_;
goto v___jp_343_;
}
}
}
v___jp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_a_344_);
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_a_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_add(v_i_324_, v___x_347_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_321_, v_as_322_, v_sz_323_, v___x_348_, v___x_346_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
return v___x_349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(lean_object* v_e_390_, lean_object* v_as_391_, lean_object* v_sz_392_, lean_object* v_i_393_, lean_object* v_b_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
size_t v_sz_boxed_405_; size_t v_i_boxed_406_; lean_object* v_res_407_; 
v_sz_boxed_405_ = lean_unbox_usize(v_sz_392_);
lean_dec(v_sz_392_);
v_i_boxed_406_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_390_, v_as_391_, v_sz_boxed_405_, v_i_boxed_406_, v_b_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v_as_391_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_e_411_, lean_object* v_as_412_, size_t v_sz_413_, size_t v_i_414_, lean_object* v_b_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec_ref(v_e_411_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_b_415_);
return v___x_422_;
}
else
{
lean_object* v_snd_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_474_; 
v_snd_423_ = lean_ctor_get(v_b_415_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_b_415_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_b_415_, 0);
lean_dec(v_unused_475_);
v___x_425_ = v_b_415_;
v_isShared_426_ = v_isSharedCheck_474_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snd_423_);
lean_dec(v_b_415_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_474_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_a_429_; lean_object* v_a_436_; 
v___x_427_ = lean_box(0);
v_a_436_ = lean_array_uget(v_as_412_, v_i_414_);
if (lean_obj_tag(v_a_436_) == 0)
{
v_a_429_ = v_snd_423_;
goto v___jp_428_;
}
else
{
lean_object* v_val_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_473_; 
v_val_437_ = lean_ctor_get(v_a_436_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_473_ == 0)
{
v___x_439_ = v_a_436_;
v_isShared_440_ = v_isSharedCheck_473_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_val_437_);
lean_dec(v_a_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_473_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_box(0);
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_443_ = l_Lean_LocalDecl_isAuxDecl(v_val_437_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = l_Lean_LocalDecl_type(v_val_437_);
lean_inc_ref(v_e_411_);
v___x_445_ = l_Lean_Meta_isExprDefEq(v___x_444_, v_e_411_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_464_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_464_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_464_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_464_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
uint8_t v___x_450_; 
v___x_450_ = lean_unbox(v_a_446_);
if (v___x_450_ == 0)
{
lean_del_object(v___x_448_);
lean_dec(v_a_446_);
lean_del_object(v___x_439_);
lean_dec(v_val_437_);
lean_dec(v_snd_423_);
v_a_429_ = v___x_442_;
goto v___jp_428_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_455_; 
lean_del_object(v___x_425_);
lean_dec_ref(v_e_411_);
v___x_451_ = l_Lean_LocalDecl_toExpr(v_val_437_);
v___x_452_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_unbox(v_a_446_);
lean_dec(v_a_446_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*1, v___x_453_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_452_);
v___x_455_ = v___x_439_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_452_);
v___x_455_ = v_reuseFailAlloc_463_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_441_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_snd_423_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_459_);
v___x_461_ = v___x_448_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_del_object(v___x_439_);
lean_dec(v_val_437_);
lean_del_object(v___x_425_);
lean_dec(v_snd_423_);
lean_dec_ref(v_e_411_);
v_a_465_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_445_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_445_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_del_object(v___x_439_);
lean_dec(v_val_437_);
lean_dec(v_snd_423_);
v_a_429_ = v___x_442_;
goto v___jp_428_;
}
}
}
v___jp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v_a_429_);
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_a_429_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
size_t v___x_432_; size_t v___x_433_; 
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_414_, v___x_432_);
v_i_414_ = v___x_433_;
v_b_415_ = v___x_431_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_e_476_, lean_object* v_as_477_, lean_object* v_sz_478_, lean_object* v_i_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
size_t v_sz_boxed_486_; size_t v_i_boxed_487_; lean_object* v_res_488_; 
v_sz_boxed_486_ = lean_unbox_usize(v_sz_478_);
lean_dec(v_sz_478_);
v_i_boxed_487_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_476_, v_as_477_, v_sz_boxed_486_, v_i_boxed_487_, v_b_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v_as_477_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(lean_object* v_e_489_, lean_object* v_as_490_, size_t v_sz_491_, size_t v_i_492_, lean_object* v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_e_489_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v_b_493_);
return v___x_505_;
}
else
{
lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_557_; 
v_snd_506_ = lean_ctor_get(v_b_493_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_b_493_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_b_493_, 0);
lean_dec(v_unused_558_);
v___x_508_ = v_b_493_;
v_isShared_509_ = v_isSharedCheck_557_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_dec(v_b_493_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_557_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_a_512_; lean_object* v_a_519_; 
v___x_510_ = lean_box(0);
v_a_519_ = lean_array_uget(v_as_490_, v_i_492_);
if (lean_obj_tag(v_a_519_) == 0)
{
v_a_512_ = v_snd_506_;
goto v___jp_511_;
}
else
{
lean_object* v_val_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_556_; 
v_val_520_ = lean_ctor_get(v_a_519_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_a_519_);
if (v_isSharedCheck_556_ == 0)
{
v___x_522_ = v_a_519_;
v_isShared_523_ = v_isSharedCheck_556_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_val_520_);
lean_dec(v_a_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_556_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_box(0);
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_526_ = l_Lean_LocalDecl_isAuxDecl(v_val_520_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = l_Lean_LocalDecl_type(v_val_520_);
lean_inc_ref(v_e_489_);
v___x_528_ = l_Lean_Meta_isExprDefEq(v___x_527_, v_e_489_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_547_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_547_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_547_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_547_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint8_t v___x_533_; 
v___x_533_ = lean_unbox(v_a_529_);
if (v___x_533_ == 0)
{
lean_del_object(v___x_531_);
lean_dec(v_a_529_);
lean_del_object(v___x_522_);
lean_dec(v_val_520_);
lean_dec(v_snd_506_);
v_a_512_ = v___x_525_;
goto v___jp_511_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___x_538_; 
lean_del_object(v___x_508_);
lean_dec_ref(v_e_489_);
v___x_534_ = l_Lean_LocalDecl_toExpr(v_val_520_);
v___x_535_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_unbox(v_a_529_);
lean_dec(v_a_529_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_536_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_535_);
v___x_538_ = v___x_522_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_535_);
v___x_538_ = v_reuseFailAlloc_546_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_524_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_snd_506_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_542_);
v___x_544_ = v___x_531_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_del_object(v___x_522_);
lean_dec(v_val_520_);
lean_del_object(v___x_508_);
lean_dec(v_snd_506_);
lean_dec_ref(v_e_489_);
v_a_548_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_528_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_528_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_del_object(v___x_522_);
lean_dec(v_val_520_);
lean_dec(v_snd_506_);
v_a_512_ = v___x_525_;
goto v___jp_511_;
}
}
}
v___jp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_a_512_);
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_512_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_add(v_i_492_, v___x_515_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_489_, v_as_490_, v_sz_491_, v___x_516_, v___x_514_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(lean_object* v_e_559_, lean_object* v_as_560_, lean_object* v_sz_561_, lean_object* v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_561_);
lean_dec(v_sz_561_);
v_i_boxed_575_ = lean_unbox_usize(v_i_562_);
lean_dec(v_i_562_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_559_, v_as_560_, v_sz_boxed_574_, v_i_boxed_575_, v_b_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v_as_560_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(lean_object* v_init_577_, lean_object* v_e_578_, lean_object* v_n_579_, lean_object* v_b_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
if (lean_obj_tag(v_n_579_) == 0)
{
lean_object* v_cs_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_625_; 
v_cs_591_ = lean_ctor_get(v_n_579_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_n_579_);
if (v_isSharedCheck_625_ == 0)
{
v___x_593_ = v_n_579_;
v_isShared_594_ = v_isSharedCheck_625_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_cs_591_);
lean_dec(v_n_579_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_625_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; size_t v_sz_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_b_580_);
v_sz_597_ = lean_array_size(v_cs_591_);
v___x_598_ = ((size_t)0ULL);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_577_, v_e_578_, v_cs_591_, v_sz_597_, v___x_598_, v___x_596_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec_ref(v_cs_591_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_616_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_616_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_616_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_616_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_fst_604_; 
v_fst_604_ = lean_ctor_get(v_a_600_, 0);
if (lean_obj_tag(v_fst_604_) == 0)
{
lean_object* v_snd_605_; lean_object* v___x_607_; 
v_snd_605_ = lean_ctor_get(v_a_600_, 1);
lean_inc(v_snd_605_);
lean_dec(v_a_600_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 1);
lean_ctor_set(v___x_593_, 0, v_snd_605_);
v___x_607_ = v___x_593_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_snd_605_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_607_);
v___x_609_ = v___x_602_;
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
}
else
{
lean_object* v_val_612_; lean_object* v___x_614_; 
lean_inc_ref(v_fst_604_);
lean_dec(v_a_600_);
lean_del_object(v___x_593_);
v_val_612_ = lean_ctor_get(v_fst_604_, 0);
lean_inc(v_val_612_);
lean_dec_ref(v_fst_604_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_val_612_);
v___x_614_ = v___x_602_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_val_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_del_object(v___x_593_);
v_a_617_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_599_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_599_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v_vs_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_660_; 
v_vs_626_ = lean_ctor_get(v_n_579_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_n_579_);
if (v_isSharedCheck_660_ == 0)
{
v___x_628_ = v_n_579_;
v_isShared_629_ = v_isSharedCheck_660_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_vs_626_);
lean_dec(v_n_579_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_660_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; size_t v_sz_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_630_ = lean_box(0);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_b_580_);
v_sz_632_ = lean_array_size(v_vs_626_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_578_, v_vs_626_, v_sz_632_, v___x_633_, v___x_631_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec_ref(v_vs_626_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_651_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_651_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_651_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_651_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_fst_639_; 
v_fst_639_ = lean_ctor_get(v_a_635_, 0);
if (lean_obj_tag(v_fst_639_) == 0)
{
lean_object* v_snd_640_; lean_object* v___x_642_; 
v_snd_640_ = lean_ctor_get(v_a_635_, 1);
lean_inc(v_snd_640_);
lean_dec(v_a_635_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_snd_640_);
v___x_642_ = v___x_628_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_snd_640_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_642_);
v___x_644_ = v___x_637_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_val_647_; lean_object* v___x_649_; 
lean_inc_ref(v_fst_639_);
lean_dec(v_a_635_);
lean_del_object(v___x_628_);
v_val_647_ = lean_ctor_get(v_fst_639_, 0);
lean_inc(v_val_647_);
lean_dec_ref(v_fst_639_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v_val_647_);
v___x_649_ = v___x_637_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_val_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_del_object(v___x_628_);
v_a_652_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_634_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_634_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(lean_object* v_init_661_, lean_object* v_e_662_, lean_object* v_as_663_, size_t v_sz_664_, size_t v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_lt(v_i_665_, v_sz_664_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec_ref(v_e_662_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_b_666_);
return v___x_678_;
}
else
{
lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_713_; 
v_snd_679_ = lean_ctor_get(v_b_666_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_b_666_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v_b_666_, 0);
lean_dec(v_unused_714_);
v___x_681_ = v_b_666_;
v_isShared_682_ = v_isSharedCheck_713_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_dec(v_b_666_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_713_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_array_uget_borrowed(v_as_663_, v_i_665_);
lean_inc(v_snd_679_);
lean_inc(v_a_683_);
lean_inc_ref(v_e_662_);
v___x_684_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_661_, v_e_662_, v_a_683_, v_snd_679_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_704_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_704_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_704_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_704_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
if (lean_obj_tag(v_a_685_) == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
lean_dec_ref(v_e_662_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_a_685_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_689_);
v___x_691_ = v___x_681_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_snd_679_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_691_);
v___x_693_ = v___x_687_;
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
else
{
lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_del_object(v___x_687_);
lean_dec(v_snd_679_);
v_a_696_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v_a_685_);
v___x_697_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_a_696_);
lean_ctor_set(v___x_681_, 0, v___x_697_);
v___x_699_ = v___x_681_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_a_696_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
size_t v___x_700_; size_t v___x_701_; 
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_add(v_i_665_, v___x_700_);
v_i_665_ = v___x_701_;
v_b_666_ = v___x_699_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_681_);
lean_dec(v_snd_679_);
lean_dec_ref(v_e_662_);
v_a_705_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_684_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_684_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(lean_object* v_init_715_, lean_object* v_e_716_, lean_object* v_as_717_, lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_sz_boxed_731_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_732_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_715_, v_e_716_, v_as_717_, v_sz_boxed_731_, v_i_boxed_732_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v_as_717_);
lean_dec_ref(v_init_715_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(lean_object* v_init_734_, lean_object* v_e_735_, lean_object* v_n_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_734_, v_e_735_, v_n_736_, v_b_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v_init_734_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(lean_object* v_e_749_, lean_object* v_t_750_, lean_object* v_init_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_root_762_; lean_object* v_tail_763_; lean_object* v___x_764_; 
v_root_762_ = lean_ctor_get(v_t_750_, 0);
lean_inc_ref(v_root_762_);
v_tail_763_ = lean_ctor_get(v_t_750_, 1);
lean_inc_ref(v_tail_763_);
lean_dec_ref(v_t_750_);
lean_inc_ref(v_e_749_);
lean_inc_ref(v_init_751_);
v___x_764_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_751_, v_e_749_, v_root_762_, v_init_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec_ref(v_init_751_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_801_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_801_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_801_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_801_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
if (lean_obj_tag(v_a_765_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; 
lean_dec_ref(v_tail_763_);
lean_dec_ref(v_e_749_);
v_a_769_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v_a_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_a_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_774_; lean_object* v___x_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
lean_del_object(v___x_767_);
v_a_773_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v_a_765_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_a_773_);
v_sz_776_ = lean_array_size(v_tail_763_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_749_, v_tail_763_, v_sz_776_, v___x_777_, v___x_775_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec_ref(v_tail_763_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_792_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_792_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_792_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_792_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_fst_783_; 
v_fst_783_ = lean_ctor_get(v_a_779_, 0);
if (lean_obj_tag(v_fst_783_) == 0)
{
lean_object* v_snd_784_; lean_object* v___x_786_; 
v_snd_784_ = lean_ctor_get(v_a_779_, 1);
lean_inc(v_snd_784_);
lean_dec(v_a_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_snd_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_snd_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_object* v_val_788_; lean_object* v___x_790_; 
lean_inc_ref(v_fst_783_);
lean_dec(v_a_779_);
v_val_788_ = lean_ctor_get(v_fst_783_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v_fst_783_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_val_788_);
v___x_790_ = v___x_781_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_788_);
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
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_793_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_778_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_778_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_tail_763_);
lean_dec_ref(v_e_749_);
v_a_802_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_764_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_764_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(lean_object* v_e_810_, lean_object* v_t_811_, lean_object* v_init_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_810_, v_t_811_, v_init_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption(lean_object* v_e_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_lctx_840_; lean_object* v_decls_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_lctx_840_ = lean_ctor_get(v_a_835_, 2);
v_decls_841_ = lean_ctor_get(v_lctx_840_, 1);
v___x_842_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0));
lean_inc_ref(v_decls_841_);
v___x_843_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_829_, v_decls_841_, v___x_842_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_857_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_857_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_857_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_857_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_fst_848_; 
v_fst_848_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_fst_848_);
lean_dec(v_a_844_);
if (lean_obj_tag(v_fst_848_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1));
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v_val_853_; lean_object* v___x_855_; 
v_val_853_ = lean_ctor_get(v_fst_848_, 0);
lean_inc(v_val_853_);
lean_dec_ref(v_fst_848_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v_val_853_);
v___x_855_ = v___x_846_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_val_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_843_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_843_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(lean_object* v_e_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(v_e_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(lean_object* v_e_878_, lean_object* v_as_879_, size_t v_sz_880_, size_t v_i_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_878_, v_as_879_, v_sz_880_, v_i_881_, v_b_882_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(lean_object* v_e_894_, lean_object* v_as_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
size_t v_sz_boxed_909_; size_t v_i_boxed_910_; lean_object* v_res_911_; 
v_sz_boxed_909_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_910_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_894_, v_as_895_, v_sz_boxed_909_, v_i_boxed_910_, v_b_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v_as_895_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(lean_object* v_e_912_, lean_object* v_as_913_, size_t v_sz_914_, size_t v_i_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_912_, v_as_913_, v_sz_914_, v_i_915_, v_b_916_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_e_928_, lean_object* v_as_929_, lean_object* v_sz_930_, lean_object* v_i_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
size_t v_sz_boxed_943_; size_t v_i_boxed_944_; lean_object* v_res_945_; 
v_sz_boxed_943_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_944_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_928_, v_as_929_, v_sz_boxed_943_, v_i_boxed_944_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v_as_929_);
return v_res_945_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
