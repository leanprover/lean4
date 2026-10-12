// Lean compiler output
// Module: Lean.Meta.KExprMap
// Imports: public import Lean.Data.AssocList public import Lean.HeadIndex public import Lean.Meta.Basic
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint64_t l_Lean_HeadIndex_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedKExprMap_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__0, &l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__0_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
lean_object* l_Lean_Meta_instInhabitedKExprMap_default___redArg(){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__1, &l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__1_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___redArg___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Meta_instInhabitedKExprMap_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_6_;
v_res_6_ = l_Lean_Meta_instInhabitedKExprMap_default___redArg();
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default___redArg___boxed(lean_object* v___dummy_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Meta_instInhabitedKExprMap_default___redArg();
return v_res_8_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_instInhabitedKExprMap_default___redArg();
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default(lean_object* v_00_u03b1_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___closed__0, &l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0);
return v___x_11_;
}
}
lean_object* l_Lean_Meta_instInhabitedKExprMap___redArg(){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___closed__0, &l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT void l_Lean_Meta_instInhabitedKExprMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_14_;
v_res_14_ = l_Lean_Meta_instInhabitedKExprMap___redArg();
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_instInhabitedKExprMap___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap(lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___closed__0, &l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_19_, lean_object* v_vals_20_, lean_object* v_i_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_array_get_size(v_keys_19_);
v___x_24_ = lean_nat_dec_lt(v_i_21_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
lean_dec(v_i_21_);
v___x_25_ = lean_box(0);
return v___x_25_;
}
else
{
lean_object* v_k_x27_26_; uint8_t v___x_27_; 
v_k_x27_26_ = lean_array_fget_borrowed(v_keys_19_, v_i_21_);
v___x_27_ = l_Lean_instBEqHeadIndex_beq(v_k_22_, v_k_x27_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_add(v_i_21_, v___x_28_);
lean_dec(v_i_21_);
v_i_21_ = v___x_29_;
goto _start;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_array_fget_borrowed(v_vals_20_, v_i_21_);
lean_dec(v_i_21_);
lean_inc(v___x_31_);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_33_, lean_object* v_vals_34_, lean_object* v_i_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_33_, v_vals_34_, v_i_35_, v_k_36_);
lean_dec(v_k_36_);
lean_dec_ref(v_vals_34_);
lean_dec_ref(v_keys_33_);
return v_res_37_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_38_, size_t v_x_39_, lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v_es_41_; lean_object* v___x_42_; size_t v___x_43_; size_t v___x_44_; lean_object* v_j_45_; lean_object* v___x_46_; 
v_es_41_ = lean_ctor_get(v_x_38_, 0);
v___x_42_ = lean_box(2);
v___x_43_ = ((size_t)31ULL);
v___x_44_ = lean_usize_land(v_x_39_, v___x_43_);
v_j_45_ = lean_usize_to_nat(v___x_44_);
v___x_46_ = lean_array_get_borrowed(v___x_42_, v_es_41_, v_j_45_);
lean_dec(v_j_45_);
switch(lean_obj_tag(v___x_46_))
{
case 0:
{
lean_object* v_key_47_; lean_object* v_val_48_; uint8_t v___x_49_; 
v_key_47_ = lean_ctor_get(v___x_46_, 0);
v_val_48_ = lean_ctor_get(v___x_46_, 1);
v___x_49_ = l_Lean_instBEqHeadIndex_beq(v_x_40_, v_key_47_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
else
{
lean_object* v___x_51_; 
lean_inc(v_val_48_);
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_val_48_);
return v___x_51_;
}
}
case 1:
{
lean_object* v_node_52_; size_t v___x_53_; size_t v___x_54_; 
v_node_52_ = lean_ctor_get(v___x_46_, 0);
v___x_53_ = ((size_t)5ULL);
v___x_54_ = lean_usize_shift_right(v_x_39_, v___x_53_);
v_x_38_ = v_node_52_;
v_x_39_ = v___x_54_;
goto _start;
}
default: 
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
}
else
{
lean_object* v_ks_57_; lean_object* v_vs_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_ks_57_ = lean_ctor_get(v_x_38_, 0);
v_vs_58_ = lean_ctor_get(v_x_38_, 1);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_57_, v_vs_58_, v___x_59_, v_x_40_);
return v___x_60_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_38_ = stack[0].m_obj;
size_t v_x_39_ = stack[1].m_num;
lean_object* v_x_40_ = stack[2].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_38_, v_x_39_, v_x_40_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
size_t v_x_1197__boxed_65_; lean_object* v_res_66_; 
v_x_1197__boxed_65_ = lean_unbox_usize(v_x_63_);
lean_dec(v_x_63_);
v_res_66_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_62_, v_x_1197__boxed_65_, v_x_64_);
lean_dec(v_x_64_);
lean_dec_ref(v_x_62_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint64_t v___x_69_; size_t v___x_70_; lean_object* v___x_71_; 
v___x_69_ = l_Lean_HeadIndex_hash(v_x_68_);
v___x_70_ = lean_uint64_to_usize(v___x_69_);
v___x_71_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_67_, v___x_70_, v_x_68_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_72_, v_x_73_);
lean_dec(v_x_73_);
lean_dec_ref(v_x_72_);
return v_res_74_;
}
}
lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(lean_object* v_e_78_, lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_86_; 
lean_dec_ref(v_e_78_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v_x_79_);
return v___x_86_;
}
else
{
lean_object* v_key_87_; lean_object* v_value_88_; lean_object* v_tail_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec_ref(v_x_79_);
v_key_87_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_key_87_);
v_value_88_ = lean_ctor_get(v_x_80_, 1);
lean_inc(v_value_88_);
v_tail_89_ = lean_ctor_get(v_x_80_, 2);
lean_inc(v_tail_89_);
lean_dec_ref_known(v_x_80_, 3);
v___x_90_ = lean_box(0);
v___x_91_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
lean_inc_ref(v_e_78_);
v___x_92_ = l_Lean_Meta_isExprDefEq(v_e_78_, v_key_87_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_105_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_105_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_105_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_105_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v___x_97_; 
v___x_97_ = lean_unbox(v_a_93_);
lean_dec(v_a_93_);
if (v___x_97_ == 0)
{
lean_del_object(v___x_95_);
lean_dec(v_value_88_);
v_x_79_ = v___x_91_;
v_x_80_ = v_tail_89_;
goto _start;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
lean_dec(v_tail_89_);
lean_dec_ref(v_e_78_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v_value_88_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_90_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_101_);
v___x_103_ = v___x_95_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_tail_89_);
lean_dec(v_value_88_);
lean_dec_ref(v_e_78_);
v_a_106_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_92_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_92_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_78_ = stack[0].m_obj;
lean_object* v_x_79_ = stack[1].m_obj;
lean_object* v_x_80_ = stack[2].m_obj;
lean_object* v___y_81_ = stack[3].m_obj;
lean_object* v___y_82_ = stack[4].m_obj;
lean_object* v___y_83_ = stack[5].m_obj;
lean_object* v___y_84_ = stack[6].m_obj;
lean_object* v_res_114_;
v_res_114_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_78_, v_x_79_, v_x_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___boxed(lean_object* v_e_115_, lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_115_, v_x_116_, v_x_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object* v_m_124_, lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_inc_ref(v_e_125_);
v___x_134_ = l_Lean_Expr_toHeadIndex(v_e_125_);
v___x_135_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_124_, v___x_134_);
lean_dec(v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_dec_ref(v_e_125_);
goto v___jp_131_;
}
else
{
lean_object* v_val_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_val_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v___x_138_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_125_, v___x_137_, v_val_136_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_fst_143_; 
v_fst_143_ = lean_ctor_get(v_a_139_, 0);
lean_inc(v_fst_143_);
lean_dec(v_a_139_);
if (lean_obj_tag(v_fst_143_) == 0)
{
lean_del_object(v___x_141_);
goto v___jp_131_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_146_; 
v_val_144_ = lean_ctor_get(v_fst_143_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v_fst_143_, 1);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v_val_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_val_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_138_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
v___jp_131_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_box(0);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_KExprMap_find_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_124_ = stack[0].m_obj;
lean_object* v_e_125_ = stack[1].m_obj;
lean_object* v_a_126_ = stack[2].m_obj;
lean_object* v_a_127_ = stack[3].m_obj;
lean_object* v_a_128_ = stack[4].m_obj;
lean_object* v_a_129_ = stack[5].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_124_, v_e_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(lean_object* v_m_158_, lean_object* v_e_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_158_, v_e_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec_ref(v_m_158_);
return v_res_165_;
}
}
lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object* v_00_u03b1_166_, lean_object* v_m_167_, lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_167_, v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_Meta_KExprMap_find_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_167_ = stack[1].m_obj;
lean_object* v_e_168_ = stack[2].m_obj;
lean_object* v_a_169_ = stack[3].m_obj;
lean_object* v_a_170_ = stack[4].m_obj;
lean_object* v_a_171_ = stack[5].m_obj;
lean_object* v_a_172_ = stack[6].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Meta_KExprMap_find_x3f(lean_box(0), v_m_167_, v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___boxed(lean_object* v_00_u03b1_176_, lean_object* v_m_177_, lean_object* v_e_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_KExprMap_find_x3f(v_00_u03b1_176_, v_m_177_, v_e_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec_ref(v_m_177_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(lean_object* v_00_u03b2_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(v_00_u03b2_189_, v_x_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec_ref(v_x_190_);
return v_res_192_;
}
}
lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_object* v_00_u03b1_193_, lean_object* v_e_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_194_, v_x_195_, v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT void l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_194_ = stack[1].m_obj;
lean_object* v_x_195_ = stack[2].m_obj;
lean_object* v_x_196_ = stack[3].m_obj;
lean_object* v___y_197_ = stack[4].m_obj;
lean_object* v___y_198_ = stack[5].m_obj;
lean_object* v___y_199_ = stack[6].m_obj;
lean_object* v___y_200_ = stack[7].m_obj;
lean_object* v_res_203_;
v_res_203_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_box(0), v_e_194_, v_x_195_, v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(lean_object* v_00_u03b1_204_, lean_object* v_e_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(v_00_u03b1_204_, v_e_205_, v_x_206_, v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, size_t v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_215_, v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_215_ = stack[1].m_obj;
size_t v_x_216_ = stack[2].m_num;
lean_object* v_x_217_ = stack[3].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_box(0), v_x_215_, v_x_216_, v_x_217_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
size_t v_x_1563__boxed_224_; lean_object* v_res_225_; 
v_x_1563__boxed_224_ = lean_unbox_usize(v_x_222_);
lean_dec(v_x_222_);
v_res_225_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_220_, v_x_221_, v_x_1563__boxed_224_, v_x_223_);
lean_dec(v_x_223_);
lean_dec_ref(v_x_221_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_heq_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_227_, v_vals_228_, v_i_230_, v_k_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_233_, lean_object* v_keys_234_, lean_object* v_vals_235_, lean_object* v_heq_236_, lean_object* v_i_237_, lean_object* v_k_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_233_, v_keys_234_, v_vals_235_, v_heq_236_, v_i_237_, v_k_238_);
lean_dec(v_k_238_);
lean_dec_ref(v_vals_235_);
lean_dec_ref(v_keys_234_);
return v_res_239_;
}
}
lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(lean_object* v_ps_240_, lean_object* v_e_241_, lean_object* v_v_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
if (lean_obj_tag(v_ps_240_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v_e_241_);
lean_ctor_set(v___x_248_, 1, v_v_242_);
lean_ctor_set(v___x_248_, 2, v_ps_240_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
else
{
lean_object* v_key_250_; lean_object* v_value_251_; lean_object* v_tail_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_289_; 
v_key_250_ = lean_ctor_get(v_ps_240_, 0);
v_value_251_ = lean_ctor_get(v_ps_240_, 1);
v_tail_252_ = lean_ctor_get(v_ps_240_, 2);
v_isSharedCheck_289_ = !lean_is_exclusive(v_ps_240_);
if (v_isSharedCheck_289_ == 0)
{
v___x_254_ = v_ps_240_;
v_isShared_255_ = v_isSharedCheck_289_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_tail_252_);
lean_inc(v_value_251_);
lean_inc(v_key_250_);
lean_dec(v_ps_240_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_289_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; 
lean_inc(v_key_250_);
lean_inc_ref(v_e_241_);
v___x_256_ = l_Lean_Meta_isExprDefEq(v_e_241_, v_key_250_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_280_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_280_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; 
v___x_261_ = lean_unbox(v_a_257_);
lean_dec(v_a_257_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_del_object(v___x_259_);
v___x_262_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_tail_252_, v_e_241_, v_v_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_273_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 2, v_a_263_);
v___x_268_ = v___x_254_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_key_250_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_value_251_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_a_263_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_268_);
v___x_270_ = v___x_265_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_del_object(v___x_254_);
lean_dec(v_value_251_);
lean_dec(v_key_250_);
return v___x_262_;
}
}
else
{
lean_object* v___x_275_; 
lean_dec(v_value_251_);
lean_dec(v_key_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_v_242_);
lean_ctor_set(v___x_254_, 0, v_e_241_);
v___x_275_ = v___x_254_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_e_241_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_tail_252_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_275_);
v___x_277_ = v___x_259_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_del_object(v___x_254_);
lean_dec(v_tail_252_);
lean_dec(v_value_251_);
lean_dec(v_key_250_);
lean_dec(v_v_242_);
lean_dec_ref(v_e_241_);
v_a_281_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_256_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_256_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_240_ = stack[0].m_obj;
lean_object* v_e_241_ = stack[1].m_obj;
lean_object* v_v_242_ = stack[2].m_obj;
lean_object* v_a_243_ = stack[3].m_obj;
lean_object* v_a_244_ = stack[4].m_obj;
lean_object* v_a_245_ = stack[5].m_obj;
lean_object* v_a_246_ = stack[6].m_obj;
lean_object* v_res_290_;
v_res_290_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_240_, v_e_241_, v_v_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(lean_object* v_ps_291_, lean_object* v_e_292_, lean_object* v_v_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_291_, v_e_292_, v_v_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_299_;
}
}
lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_object* v_00_u03b1_300_, lean_object* v_ps_301_, lean_object* v_e_302_, lean_object* v_v_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_301_, v_e_302_, v_v_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
return v___x_309_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_301_ = stack[1].m_obj;
lean_object* v_e_302_ = stack[2].m_obj;
lean_object* v_v_303_ = stack[3].m_obj;
lean_object* v_a_304_ = stack[4].m_obj;
lean_object* v_a_305_ = stack[5].m_obj;
lean_object* v_a_306_ = stack[6].m_obj;
lean_object* v_a_307_ = stack[7].m_obj;
lean_object* v_res_310_;
v_res_310_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_box(0), v_ps_301_, v_e_302_, v_v_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(lean_object* v_00_u03b1_311_, lean_object* v_ps_312_, lean_object* v_e_313_, lean_object* v_v_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(v_00_u03b1_311_, v_ps_312_, v_e_313_, v_v_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_350_; 
v_ks_325_ = lean_ctor_get(v_x_321_, 0);
v_vs_326_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_350_ == 0)
{
v___x_328_ = v_x_321_;
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_vs_326_);
lean_inc(v_ks_325_);
lean_dec(v_x_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_get_size(v_ks_325_);
v___x_331_ = lean_nat_dec_lt(v_x_322_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec(v_x_322_);
v___x_332_ = lean_array_push(v_ks_325_, v_x_323_);
v___x_333_ = lean_array_push(v_vs_326_, v_x_324_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
lean_ctor_set(v___x_328_, 0, v___x_332_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v_k_x27_337_; uint8_t v___x_338_; 
v_k_x27_337_ = lean_array_fget_borrowed(v_ks_325_, v_x_322_);
v___x_338_ = l_Lean_instBEqHeadIndex_beq(v_x_323_, v_k_x27_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_340_; 
if (v_isShared_329_ == 0)
{
v___x_340_ = v___x_328_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_ks_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_vs_326_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v_x_322_, v___x_341_);
lean_dec(v_x_322_);
v_x_321_ = v___x_340_;
v_x_322_ = v___x_342_;
goto _start;
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = lean_array_fset(v_ks_325_, v_x_322_, v_x_323_);
v___x_346_ = lean_array_fset(v_vs_326_, v_x_322_, v_x_324_);
lean_dec(v_x_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_346_);
lean_ctor_set(v___x_328_, 0, v___x_345_);
v___x_348_ = v___x_328_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_351_, lean_object* v_k_352_, lean_object* v_v_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_351_, v___x_354_, v_k_352_, v_v_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_356_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(lean_object* v_x_357_, size_t v_x_358_, size_t v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v_es_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v_j_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_es_362_ = lean_ctor_get(v_x_357_, 0);
v___x_363_ = ((size_t)31ULL);
v___x_364_ = lean_usize_land(v_x_358_, v___x_363_);
v_j_365_ = lean_usize_to_nat(v___x_364_);
v___x_366_ = lean_array_get_size(v_es_362_);
v___x_367_ = lean_nat_dec_lt(v_j_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_dec(v_j_365_);
lean_dec(v_x_361_);
lean_dec(v_x_360_);
return v_x_357_;
}
else
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_406_; 
lean_inc_ref(v_es_362_);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_x_357_, 0);
lean_dec(v_unused_407_);
v___x_369_ = v_x_357_;
v_isShared_370_ = v_isSharedCheck_406_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_406_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_v_371_; lean_object* v___x_372_; lean_object* v_xs_x27_373_; lean_object* v___y_375_; 
v_v_371_ = lean_array_fget(v_es_362_, v_j_365_);
v___x_372_ = lean_box(0);
v_xs_x27_373_ = lean_array_fset(v_es_362_, v_j_365_, v___x_372_);
switch(lean_obj_tag(v_v_371_))
{
case 0:
{
lean_object* v_key_380_; lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_391_; 
v_key_380_ = lean_ctor_get(v_v_371_, 0);
v_val_381_ = lean_ctor_get(v_v_371_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_v_371_);
if (v_isSharedCheck_391_ == 0)
{
v___x_383_ = v_v_371_;
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_inc(v_key_380_);
lean_dec(v_v_371_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; 
v___x_385_ = l_Lean_instBEqHeadIndex_beq(v_x_360_, v_key_380_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_del_object(v___x_383_);
v___x_386_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_380_, v_val_381_, v_x_360_, v_x_361_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
v___y_375_ = v___x_387_;
goto v___jp_374_;
}
else
{
lean_object* v___x_389_; 
lean_dec(v_val_381_);
lean_dec(v_key_380_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_x_361_);
lean_ctor_set(v___x_383_, 0, v_x_360_);
v___x_389_ = v___x_383_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_x_360_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_x_361_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v___y_375_ = v___x_389_;
goto v___jp_374_;
}
}
}
}
case 1:
{
lean_object* v_node_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_node_392_ = lean_ctor_get(v_v_371_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_v_371_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v_v_371_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_node_392_);
lean_dec(v_v_371_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_usize_shift_right(v_x_358_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_x_359_, v___x_398_);
v___x_400_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_node_392_, v___x_397_, v___x_399_, v_x_360_, v_x_361_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_400_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
v___y_375_ = v___x_402_;
goto v___jp_374_;
}
}
}
default: 
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_x_360_);
lean_ctor_set(v___x_405_, 1, v_x_361_);
v___y_375_ = v___x_405_;
goto v___jp_374_;
}
}
v___jp_374_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_array_fset(v_xs_x27_373_, v_j_365_, v___y_375_);
lean_dec(v_j_365_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_376_);
v___x_378_ = v___x_369_;
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
lean_object* v_ks_408_; lean_object* v_vs_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_427_; 
v_ks_408_ = lean_ctor_get(v_x_357_, 0);
v_vs_409_ = lean_ctor_get(v_x_357_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_427_ == 0)
{
v___x_411_ = v_x_357_;
v_isShared_412_ = v_isSharedCheck_427_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_vs_409_);
lean_inc(v_ks_408_);
lean_dec(v_x_357_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_427_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_ks_408_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_vs_409_);
v___x_414_ = v_reuseFailAlloc_426_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v_newNode_415_; size_t v___x_416_; uint8_t v___x_417_; 
v_newNode_415_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v___x_414_, v_x_360_, v_x_361_);
v___x_416_ = ((size_t)7ULL);
v___x_417_ = lean_usize_dec_le(v___x_416_, v_x_359_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_418_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_415_);
v___x_419_ = lean_unsigned_to_nat(4u);
v___x_420_ = lean_nat_dec_lt(v___x_418_, v___x_419_);
lean_dec(v___x_418_);
if (v___x_420_ == 0)
{
lean_object* v_ks_421_; lean_object* v_vs_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_ks_421_ = lean_ctor_get(v_newNode_415_, 0);
lean_inc_ref(v_ks_421_);
v_vs_422_ = lean_ctor_get(v_newNode_415_, 1);
lean_inc_ref(v_vs_422_);
lean_dec_ref(v_newNode_415_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
v___x_425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_359_, v_ks_421_, v_vs_422_, v___x_423_, v___x_424_);
lean_dec_ref(v_vs_422_);
lean_dec_ref(v_ks_421_);
return v___x_425_;
}
else
{
return v_newNode_415_;
}
}
else
{
return v_newNode_415_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_357_ = stack[0].m_obj;
size_t v_x_358_ = stack[1].m_num;
size_t v_x_359_ = stack[2].m_num;
lean_object* v_x_360_ = stack[3].m_obj;
lean_object* v_x_361_ = stack[4].m_obj;
lean_object* v_res_428_;
v_res_428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_357_, v_x_358_, v_x_359_, v_x_360_, v_x_361_);
stack->m_obj
 = v_res_428_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_429_, lean_object* v_keys_430_, lean_object* v_vals_431_, lean_object* v_i_432_, lean_object* v_entries_433_){
_start:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_array_get_size(v_keys_430_);
v___x_435_ = lean_nat_dec_lt(v_i_432_, v___x_434_);
if (v___x_435_ == 0)
{
lean_dec(v_i_432_);
return v_entries_433_;
}
else
{
lean_object* v_k_436_; lean_object* v_v_437_; uint64_t v___x_438_; size_t v_h_439_; size_t v___x_440_; lean_object* v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v_h_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_k_436_ = lean_array_fget_borrowed(v_keys_430_, v_i_432_);
v_v_437_ = lean_array_fget_borrowed(v_vals_431_, v_i_432_);
v___x_438_ = l_Lean_HeadIndex_hash(v_k_436_);
v_h_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = ((size_t)5ULL);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_sub(v_depth_429_, v___x_442_);
v___x_444_ = lean_usize_mul(v___x_440_, v___x_443_);
v_h_445_ = lean_usize_shift_right(v_h_439_, v___x_444_);
v___x_446_ = lean_nat_add(v_i_432_, v___x_441_);
lean_dec(v_i_432_);
lean_inc(v_v_437_);
lean_inc(v_k_436_);
v___x_447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_entries_433_, v_h_445_, v_depth_429_, v_k_436_, v_v_437_);
v_i_432_ = v___x_446_;
v_entries_433_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_429_ = stack[0].m_num;
lean_object* v_keys_430_ = stack[1].m_obj;
lean_object* v_vals_431_ = stack[2].m_obj;
lean_object* v_i_432_ = stack[3].m_obj;
lean_object* v_entries_433_ = stack[4].m_obj;
lean_object* v_res_449_;
v_res_449_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_429_, v_keys_430_, v_vals_431_, v_i_432_, v_entries_433_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_450_, lean_object* v_keys_451_, lean_object* v_vals_452_, lean_object* v_i_453_, lean_object* v_entries_454_){
_start:
{
size_t v_depth_boxed_455_; lean_object* v_res_456_; 
v_depth_boxed_455_ = lean_unbox_usize(v_depth_450_);
lean_dec(v_depth_450_);
v_res_456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_455_, v_keys_451_, v_vals_452_, v_i_453_, v_entries_454_);
lean_dec_ref(v_vals_452_);
lean_dec_ref(v_keys_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
size_t v_x_769__boxed_462_; size_t v_x_770__boxed_463_; lean_object* v_res_464_; 
v_x_769__boxed_462_ = lean_unbox_usize(v_x_458_);
lean_dec(v_x_458_);
v_x_770__boxed_463_ = lean_unbox_usize(v_x_459_);
lean_dec(v_x_459_);
v_res_464_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_457_, v_x_769__boxed_462_, v_x_770__boxed_463_, v_x_460_, v_x_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
uint64_t v___x_468_; size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_468_ = l_Lean_HeadIndex_hash(v_x_466_);
v___x_469_ = lean_uint64_to_usize(v___x_468_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_465_, v___x_469_, v___x_470_, v_x_466_, v_x_467_);
return v___x_471_;
}
}
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object* v_m_472_, lean_object* v_e_473_, lean_object* v_v_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_k_480_; lean_object* v___x_481_; 
lean_inc_ref(v_e_473_);
v_k_480_ = l_Lean_Expr_toHeadIndex(v_e_473_);
v___x_481_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_472_, v_k_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v_e_473_);
lean_ctor_set(v___x_483_, 1, v_v_474_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
v___x_484_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_472_, v_k_480_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; 
v_val_486_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_481_, 1);
v___x_487_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_val_486_, v_e_473_, v_v_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_472_, v_k_480_, v_a_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_k_480_);
lean_dec_ref(v_m_472_);
v_a_497_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_487_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_487_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_KExprMap_insert___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_472_ = stack[0].m_obj;
lean_object* v_e_473_ = stack[1].m_obj;
lean_object* v_v_474_ = stack[2].m_obj;
lean_object* v_a_475_ = stack[3].m_obj;
lean_object* v_a_476_ = stack[4].m_obj;
lean_object* v_a_477_ = stack[5].m_obj;
lean_object* v_a_478_ = stack[6].m_obj;
lean_object* v_res_505_;
v_res_505_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_472_, v_e_473_, v_v_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
stack->m_obj
 = v_res_505_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg___boxed(lean_object* v_m_506_, lean_object* v_e_507_, lean_object* v_v_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_506_, v_e_507_, v_v_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_514_;
}
}
lean_object* l_Lean_Meta_KExprMap_insert(lean_object* v_00_u03b1_515_, lean_object* v_m_516_, lean_object* v_e_517_, lean_object* v_v_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_516_, v_e_517_, v_v_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
return v___x_524_;
}
}
LEAN_EXPORT void l_Lean_Meta_KExprMap_insert_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_516_ = stack[1].m_obj;
lean_object* v_e_517_ = stack[2].m_obj;
lean_object* v_v_518_ = stack[3].m_obj;
lean_object* v_a_519_ = stack[4].m_obj;
lean_object* v_a_520_ = stack[5].m_obj;
lean_object* v_a_521_ = stack[6].m_obj;
lean_object* v_a_522_ = stack[7].m_obj;
lean_object* v_res_525_;
v_res_525_ = l_Lean_Meta_KExprMap_insert(lean_box(0), v_m_516_, v_e_517_, v_v_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___boxed(lean_object* v_00_u03b1_526_, lean_object* v_m_527_, lean_object* v_e_528_, lean_object* v_v_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Meta_KExprMap_insert(v_00_u03b1_526_, v_m_527_, v_e_528_, v_v_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(lean_object* v_00_u03b2_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_x_537_, v_x_538_, v_x_539_);
return v___x_540_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_object* v_00_u03b2_541_, lean_object* v_x_542_, size_t v_x_543_, size_t v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_542_, v_x_543_, v_x_544_, v_x_545_, v_x_546_);
return v___x_547_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_542_ = stack[1].m_obj;
size_t v_x_543_ = stack[2].m_num;
size_t v_x_544_ = stack[3].m_num;
lean_object* v_x_545_ = stack[4].m_obj;
lean_object* v_x_546_ = stack[5].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_box(0), v_x_542_, v_x_543_, v_x_544_, v_x_545_, v_x_546_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
size_t v_x_1123__boxed_555_; size_t v_x_1124__boxed_556_; lean_object* v_res_557_; 
v_x_1123__boxed_555_ = lean_unbox_usize(v_x_551_);
lean_dec(v_x_551_);
v_x_1124__boxed_556_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_res_557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_549_, v_x_550_, v_x_1123__boxed_555_, v_x_1124__boxed_556_, v_x_553_, v_x_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_558_, lean_object* v_n_559_, lean_object* v_k_560_, lean_object* v_v_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_559_, v_k_560_, v_v_561_);
return v___x_562_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_563_, size_t v_depth_564_, lean_object* v_keys_565_, lean_object* v_vals_566_, lean_object* v_heq_567_, lean_object* v_i_568_, lean_object* v_entries_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_564_, v_keys_565_, v_vals_566_, v_i_568_, v_entries_569_);
return v___x_570_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_564_ = stack[1].m_num;
lean_object* v_keys_565_ = stack[2].m_obj;
lean_object* v_vals_566_ = stack[3].m_obj;
lean_object* v_i_568_ = stack[5].m_obj;
lean_object* v_entries_569_ = stack[6].m_obj;
lean_object* v_res_571_;
v_res_571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_box(0), v_depth_564_, v_keys_565_, v_vals_566_, lean_box(0), v_i_568_, v_entries_569_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_572_, lean_object* v_depth_573_, lean_object* v_keys_574_, lean_object* v_vals_575_, lean_object* v_heq_576_, lean_object* v_i_577_, lean_object* v_entries_578_){
_start:
{
size_t v_depth_boxed_579_; lean_object* v_res_580_; 
v_depth_boxed_579_ = lean_unbox_usize(v_depth_573_);
lean_dec(v_depth_573_);
v_res_580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_572_, v_depth_boxed_579_, v_keys_574_, v_vals_575_, v_heq_576_, v_i_577_, v_entries_578_);
lean_dec_ref(v_vals_575_);
lean_dec_ref(v_keys_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_582_, v_x_583_, v_x_584_, v_x_585_);
return v___x_586_;
}
}
lean_object* runtime_initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_AssocList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_KExprMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_AssocList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KExprMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_KExprMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_KExprMap(builtin);
}
#ifdef __cplusplus
}
#endif
