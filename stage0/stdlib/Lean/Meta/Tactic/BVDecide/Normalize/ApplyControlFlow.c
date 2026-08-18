// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
// Imports: public import Lean.Meta.Tactic.Simp import Init.ByCases import Init.Omega public import Lean.Meta.Sym.Simp.SimpM
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "apply_ite"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(228, 253, 97, 171, 128, 176, 200, 75)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "apply_cond"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 139, 57, 144, 52, 240, 188, 35)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_name_eq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___y_63_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
if (lean_obj_tag(v_query_59_) == 0)
{
uint64_t v___x_78_; 
v___x_78_ = 1723ULL;
v___y_63_ = v___x_78_;
goto v___jp_62_;
}
else
{
uint64_t v_hash_79_; 
v_hash_79_ = lean_ctor_get_uint64(v_query_59_, sizeof(void*)*2);
v___y_63_ = v_hash_79_;
goto v___jp_62_;
}
v___jp_62_:
{
uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v_fold_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_64_ = 32ULL;
v___x_65_ = lean_uint64_shift_right(v___y_63_, v___x_64_);
v_fold_66_ = lean_uint64_xor(v___y_63_, v___x_65_);
v___x_67_ = 16ULL;
v___x_68_ = lean_uint64_shift_right(v_fold_66_, v___x_67_);
v___x_69_ = lean_uint64_xor(v_fold_66_, v___x_68_);
v___x_70_ = lean_uint64_to_usize(v___x_69_);
v___x_71_ = lean_usize_of_nat(v___x_61_);
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_sub(v___x_71_, v___x_72_);
v___x_74_ = lean_usize_land(v___x_70_, v___x_73_);
v___x_75_ = lean_usize_to_nat(v___x_74_);
v___x_76_ = lean_box(0);
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg(v_m_58_, v_query_59_, v___x_76_, v___x_61_, v___x_75_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg(v_m_80_, v_query_81_);
lean_dec(v_query_81_);
lean_dec_ref(v_m_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(lean_object* v_m_83_, lean_object* v_query_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg(v_m_83_, v_query_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_index_86_; lean_object* v_key_87_; lean_object* v_value_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_index_86_ = lean_ctor_get(v___x_85_, 0);
v_key_87_ = lean_ctor_get(v___x_85_, 1);
v_value_88_ = lean_ctor_get(v___x_85_, 2);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_85_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_value_88_);
lean_inc(v_key_87_);
lean_inc(v_index_86_);
lean_dec(v___x_85_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_index_86_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_key_87_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_value_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v___x_85_);
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_m_97_, lean_object* v_query_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_m_97_, v_query_98_);
lean_dec(v_query_98_);
lean_dec_ref(v_m_97_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(lean_object* v_m_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_m_100_, v_a_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
uint8_t v___x_103_; 
lean_dec_ref_known(v___x_102_, 3);
v___x_103_ = 1;
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___boxed(lean_object* v_m_105_, lean_object* v_a_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_m_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_m_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_unsigned_to_nat(5u);
v___x_114_ = lean_mk_empty_array_with_capacity(v___x_113_);
v___x_115_ = lean_array_push(v___x_114_, v___x_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(lean_object* v_headSyms_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
if (lean_obj_tag(v_x_122_) == 5)
{
lean_object* v_fn_132_; lean_object* v_arg_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_fn_132_ = lean_ctor_get(v_x_122_, 0);
lean_inc_ref(v_fn_132_);
v_arg_133_ = lean_ctor_get(v_x_122_, 1);
lean_inc_ref(v_arg_133_);
lean_dec_ref_known(v_x_122_, 2);
v___x_134_ = lean_array_set(v_x_123_, v_x_124_, v_arg_133_);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_sub(v_x_124_, v___x_135_);
lean_dec(v_x_124_);
v_x_122_ = v_fn_132_;
v_x_123_ = v___x_134_;
v_x_124_ = v___x_136_;
goto _start;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
lean_dec(v_x_124_);
v___x_138_ = lean_array_get_size(v_x_123_);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_nat_dec_eq(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_sub(v___x_138_, v___x_144_);
v___x_146_ = lean_array_fget_borrowed(v_x_123_, v___x_145_);
lean_dec(v___x_145_);
lean_inc(v___x_146_);
v___x_147_ = l_Lean_Expr_cleanupAnnotations(v___x_146_);
v___x_148_ = l_Lean_Expr_isApp(v___x_147_);
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_147_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
goto v___jp_141_;
}
else
{
lean_object* v_arg_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_arg_149_ = lean_ctor_get(v___x_147_, 1);
lean_inc_ref(v_arg_149_);
v___x_150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_147_);
v___x_151_ = l_Lean_Expr_isApp(v___x_150_);
if (v___x_151_ == 0)
{
lean_dec_ref(v___x_150_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
goto v___jp_141_;
}
else
{
lean_object* v_arg_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_arg_152_ = lean_ctor_get(v___x_150_, 1);
lean_inc_ref(v_arg_152_);
v___x_153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_150_);
v___x_154_ = l_Lean_Expr_isApp(v___x_153_);
if (v___x_154_ == 0)
{
lean_dec_ref(v___x_153_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
goto v___jp_141_;
}
else
{
lean_object* v_arg_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_arg_155_ = lean_ctor_get(v___x_153_, 1);
lean_inc_ref(v_arg_155_);
v___x_156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_153_);
v___x_157_ = l_Lean_Expr_isApp(v___x_156_);
if (v___x_157_ == 0)
{
lean_dec_ref(v___x_156_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
goto v___jp_141_;
}
else
{
lean_object* v_arg_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_arg_158_ = lean_ctor_get(v___x_156_, 1);
lean_inc_ref(v_arg_158_);
v___x_159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_156_);
v___x_160_ = l_Lean_Expr_isApp(v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v___x_159_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
goto v___jp_141_;
}
else
{
lean_object* v_arg_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_arg_161_ = lean_ctor_get(v___x_159_, 1);
lean_inc_ref(v_arg_161_);
v___x_162_ = l_Lean_Expr_appFnCleanup___redArg(v___x_159_);
v___x_163_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__1));
v___x_164_ = l_Lean_Expr_isConstOf(v___x_162_, v___x_163_);
lean_dec_ref(v___x_162_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_arg_161_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
goto v___jp_141_;
}
else
{
if (lean_obj_tag(v_x_122_) == 4)
{
lean_object* v_declName_165_; uint8_t v___x_166_; 
v_declName_165_ = lean_ctor_get(v_x_122_, 0);
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_headSyms_121_, v_declName_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref_known(v_x_122_, 2);
lean_dec_ref(v_arg_161_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
v___x_167_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_167_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
else
{
lean_object* v_params_169_; lean_object* v_fnApp_170_; lean_object* v_newT_171_; lean_object* v_newE_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_params_169_ = lean_array_pop(v_x_123_);
v_fnApp_170_ = l_Lean_mkAppN(v_x_122_, v_params_169_);
lean_dec_ref(v_params_169_);
lean_inc_ref(v_arg_152_);
lean_inc_ref_n(v_fnApp_170_, 2);
v_newT_171_ = l_Lean_Expr_app___override(v_fnApp_170_, v_arg_152_);
lean_inc_ref(v_arg_149_);
v_newE_172_ = l_Lean_Expr_app___override(v_fnApp_170_, v_arg_149_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_arg_158_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v_arg_155_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_newT_171_);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v_newE_172_);
v___x_178_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__2);
lean_inc_ref(v___x_174_);
v___x_179_ = lean_array_push(v___x_178_, v___x_174_);
lean_inc_ref(v___x_175_);
v___x_180_ = lean_array_push(v___x_179_, v___x_175_);
v___x_181_ = lean_array_push(v___x_180_, v___x_176_);
v___x_182_ = lean_array_push(v___x_181_, v___x_177_);
v___x_183_ = l_Lean_Meta_mkAppOptM(v___x_163_, v___x_182_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v___x_185_ = l_Lean_Meta_Sym_shareCommonInc(v_a_184_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__4));
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v_arg_161_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_fnApp_170_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_arg_152_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_arg_149_);
v___x_192_ = lean_unsigned_to_nat(7u);
v___x_193_ = lean_mk_empty_array_with_capacity(v___x_192_);
v___x_194_ = lean_array_push(v___x_193_, v___x_188_);
v___x_195_ = lean_array_push(v___x_194_, v___x_173_);
v___x_196_ = lean_array_push(v___x_195_, v___x_189_);
v___x_197_ = lean_array_push(v___x_196_, v___x_174_);
v___x_198_ = lean_array_push(v___x_197_, v___x_175_);
v___x_199_ = lean_array_push(v___x_198_, v___x_190_);
v___x_200_ = lean_array_push(v___x_199_, v___x_191_);
v___x_201_ = l_Lean_Meta_mkAppOptM(v___x_187_, v___x_200_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_206_, 0, v_a_186_);
lean_ctor_set(v___x_206_, 1, v_a_202_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*2, v___x_140_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*2 + 1, v___x_140_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_a_186_);
v_a_211_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_201_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_201_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref_known(v___x_175_, 1);
lean_dec_ref_known(v___x_174_, 1);
lean_dec_ref(v_fnApp_170_);
lean_dec_ref(v_arg_161_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
v_a_219_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_185_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_185_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref_known(v___x_175_, 1);
lean_dec_ref_known(v___x_174_, 1);
lean_dec_ref(v_fnApp_170_);
lean_dec_ref(v_arg_161_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
v_a_227_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_183_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_183_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref(v_arg_161_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
v___x_235_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_235_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_235_, 1, v___x_140_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
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
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
v___x_237_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5));
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
v___jp_141_:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, 1, v___x_140_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___boxed(lean_object* v_headSyms_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_239_, v_x_240_, v_x_241_, v_x_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec_ref(v_headSyms_239_);
return v_res_250_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v_dummy_252_; 
v___x_251_ = lean_box(0);
v_dummy_252_ = l_Lean_Expr_sort___override(v___x_251_);
return v_dummy_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(lean_object* v_headSyms_253_, lean_object* v_e_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_dummy_265_; lean_object* v_nargs_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_dummy_265_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0);
v_nargs_266_ = l_Lean_Expr_getAppNumArgs(v_e_254_);
lean_inc(v_nargs_266_);
v___x_267_ = lean_mk_array(v_nargs_266_, v_dummy_265_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_sub(v_nargs_266_, v___x_268_);
lean_dec(v_nargs_266_);
v___x_270_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_253_, v_e_254_, v___x_267_, v___x_269_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object* v_headSyms_271_, lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(v_headSyms_271_, v_e_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_headSyms_271_);
return v_res_283_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(lean_object* v_00_u03b2_284_, lean_object* v_m_285_, lean_object* v_a_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_m_285_, v_a_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___boxed(lean_object* v_00_u03b2_288_, lean_object* v_m_289_, lean_object* v_a_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(v_00_u03b2_288_, v_m_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_m_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(lean_object* v_headSyms_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg(v_headSyms_293_, v_x_294_, v_x_295_, v_x_296_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___boxed(lean_object* v_headSyms_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1(v_headSyms_308_, v_x_309_, v_x_310_, v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v_headSyms_308_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(lean_object* v_00_u03b2_323_, lean_object* v_m_324_, lean_object* v_query_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___redArg(v_m_324_, v_query_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_query_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0(v_00_u03b2_327_, v_m_328_, v_query_329_);
lean_dec(v_query_329_);
lean_dec_ref(v_m_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_331_, lean_object* v_m_332_, lean_object* v_query_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___redArg(v_m_332_, v_query_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_335_, lean_object* v_m_336_, lean_object* v_query_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1(v_00_u03b2_335_, v_m_336_, v_query_337_);
lean_dec(v_query_337_);
lean_dec_ref(v_m_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_339_, lean_object* v_m_340_, lean_object* v_query_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___redArg(v_m_340_, v_query_341_, v_x_342_, v_x_343_, v_x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_347_, lean_object* v_m_348_, lean_object* v_query_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_347_, v_m_348_, v_query_349_, v_x_350_, v_x_351_, v_x_352_, v_x_353_);
lean_dec(v_query_349_);
lean_dec_ref(v_m_348_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_box(0);
v___x_359_ = lean_unsigned_to_nat(4u);
v___x_360_ = lean_mk_empty_array_with_capacity(v___x_359_);
v___x_361_ = lean_array_push(v___x_360_, v___x_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(lean_object* v_headSyms_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
if (lean_obj_tag(v_x_368_) == 5)
{
lean_object* v_fn_378_; lean_object* v_arg_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_fn_378_ = lean_ctor_get(v_x_368_, 0);
lean_inc_ref(v_fn_378_);
v_arg_379_ = lean_ctor_get(v_x_368_, 1);
lean_inc_ref(v_arg_379_);
lean_dec_ref_known(v_x_368_, 2);
v___x_380_ = lean_array_set(v_x_369_, v_x_370_, v_arg_379_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_sub(v_x_370_, v___x_381_);
lean_dec(v_x_370_);
v_x_368_ = v_fn_378_;
v_x_369_ = v___x_380_;
v_x_370_ = v___x_382_;
goto _start;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_dec(v_x_370_);
v___x_384_ = lean_array_get_size(v_x_369_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_nat_dec_eq(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_sub(v___x_384_, v___x_390_);
v___x_392_ = lean_array_fget_borrowed(v_x_369_, v___x_391_);
lean_dec(v___x_391_);
lean_inc(v___x_392_);
v___x_393_ = l_Lean_Expr_cleanupAnnotations(v___x_392_);
v___x_394_ = l_Lean_Expr_isApp(v___x_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v___x_393_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
goto v___jp_387_;
}
else
{
lean_object* v_arg_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_arg_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc_ref(v_arg_395_);
v___x_396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_393_);
v___x_397_ = l_Lean_Expr_isApp(v___x_396_);
if (v___x_397_ == 0)
{
lean_dec_ref(v___x_396_);
lean_dec_ref(v_arg_395_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
goto v___jp_387_;
}
else
{
lean_object* v_arg_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_arg_398_ = lean_ctor_get(v___x_396_, 1);
lean_inc_ref(v_arg_398_);
v___x_399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_396_);
v___x_400_ = l_Lean_Expr_isApp(v___x_399_);
if (v___x_400_ == 0)
{
lean_dec_ref(v___x_399_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
goto v___jp_387_;
}
else
{
lean_object* v_arg_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_arg_401_ = lean_ctor_get(v___x_399_, 1);
lean_inc_ref(v_arg_401_);
v___x_402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_399_);
v___x_403_ = l_Lean_Expr_isApp(v___x_402_);
if (v___x_403_ == 0)
{
lean_dec_ref(v___x_402_);
lean_dec_ref(v_arg_401_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
goto v___jp_387_;
}
else
{
lean_object* v_arg_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_arg_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc_ref(v_arg_404_);
v___x_405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_402_);
v___x_406_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1));
v___x_407_ = l_Lean_Expr_isConstOf(v___x_405_, v___x_406_);
lean_dec_ref(v___x_405_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_arg_404_);
lean_dec_ref(v_arg_401_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
goto v___jp_387_;
}
else
{
if (lean_obj_tag(v_x_368_) == 4)
{
lean_object* v_declName_408_; uint8_t v___x_409_; 
v_declName_408_ = lean_ctor_get(v_x_368_, 0);
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_headSyms_367_, v_declName_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref_known(v_x_368_, 2);
lean_dec_ref(v_arg_404_);
lean_dec_ref(v_arg_401_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
lean_dec_ref(v_x_369_);
v___x_410_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_410_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_params_412_; lean_object* v_fnApp_413_; lean_object* v_newT_414_; lean_object* v_newE_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_params_412_ = lean_array_pop(v_x_369_);
v_fnApp_413_ = l_Lean_mkAppN(v_x_368_, v_params_412_);
lean_dec_ref(v_params_412_);
lean_inc_ref(v_arg_398_);
lean_inc_ref_n(v_fnApp_413_, 2);
v_newT_414_ = l_Lean_Expr_app___override(v_fnApp_413_, v_arg_398_);
lean_inc_ref(v_arg_395_);
v_newE_415_ = l_Lean_Expr_app___override(v_fnApp_413_, v_arg_395_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_arg_401_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_newT_414_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_newE_415_);
v___x_420_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2);
lean_inc_ref(v___x_417_);
v___x_421_ = lean_array_push(v___x_420_, v___x_417_);
v___x_422_ = lean_array_push(v___x_421_, v___x_418_);
v___x_423_ = lean_array_push(v___x_422_, v___x_419_);
v___x_424_ = l_Lean_Meta_mkAppOptM(v___x_406_, v___x_423_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = l_Lean_Meta_Sym_shareCommonInc(v_a_425_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5));
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_arg_404_);
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v_fnApp_413_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_arg_398_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_arg_395_);
v___x_433_ = lean_unsigned_to_nat(6u);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_435_ = lean_array_push(v___x_434_, v___x_429_);
v___x_436_ = lean_array_push(v___x_435_, v___x_416_);
v___x_437_ = lean_array_push(v___x_436_, v___x_430_);
v___x_438_ = lean_array_push(v___x_437_, v___x_417_);
v___x_439_ = lean_array_push(v___x_438_, v___x_431_);
v___x_440_ = lean_array_push(v___x_439_, v___x_432_);
v___x_441_ = l_Lean_Meta_mkAppOptM(v___x_428_, v___x_440_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_446_, 0, v_a_427_);
lean_ctor_set(v___x_446_, 1, v_a_442_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*2, v___x_386_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*2 + 1, v___x_386_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_427_);
v_a_451_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_441_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_441_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref_known(v___x_417_, 1);
lean_dec_ref(v_fnApp_413_);
lean_dec_ref(v_arg_404_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
v_a_459_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_426_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_426_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
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
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref_known(v___x_417_, 1);
lean_dec_ref(v_fnApp_413_);
lean_dec_ref(v_arg_404_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
v_a_467_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_424_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_424_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v_arg_404_);
lean_dec_ref(v_arg_401_);
lean_dec_ref(v_arg_398_);
lean_dec_ref(v_arg_395_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
v___x_475_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_475_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_475_, 1, v___x_386_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
v___x_477_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__1___redArg___closed__5));
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
v___jp_387_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_388_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_388_, 1, v___x_386_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___boxed(lean_object* v_headSyms_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_479_, v_x_480_, v_x_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_headSyms_479_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(lean_object* v_headSyms_491_, lean_object* v_e_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_dummy_503_; lean_object* v_nargs_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_dummy_503_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0);
v_nargs_504_ = l_Lean_Expr_getAppNumArgs(v_e_492_);
lean_inc(v_nargs_504_);
v___x_505_ = lean_mk_array(v_nargs_504_, v_dummy_503_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_sub(v_nargs_504_, v___x_506_);
lean_dec(v_nargs_504_);
v___x_508_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_491_, v_e_492_, v___x_505_, v___x_507_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object* v_headSyms_509_, lean_object* v_e_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(v_headSyms_509_, v_e_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_headSyms_509_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(lean_object* v_headSyms_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_headSyms_522_, v_x_523_, v_x_524_, v_x_525_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___boxed(lean_object* v_headSyms_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(v_headSyms_537_, v_x_538_, v_x_539_, v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v_headSyms_537_);
return v_res_551_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif
