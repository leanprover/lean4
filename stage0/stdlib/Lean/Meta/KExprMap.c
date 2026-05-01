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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint64_t l_Lean_HeadIndex_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedKExprMap_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedKExprMap_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedKExprMap_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedKExprMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedKExprMap___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1;
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
static lean_object* _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___closed__0, &l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default(lean_object* v_00_u03b1_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap_default___closed__1, &l_Lean_Meta_instInhabitedKExprMap_default___closed__1_once, _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__1);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedKExprMap___closed__0(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Meta_instInhabitedKExprMap_default(lean_box(0));
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap(lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&l_Lean_Meta_instInhabitedKExprMap___closed__0, &l_Lean_Meta_instInhabitedKExprMap___closed__0_once, _init_l_Lean_Meta_instInhabitedKExprMap___closed__0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_9_, lean_object* v_vals_10_, lean_object* v_i_11_, lean_object* v_k_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = lean_array_get_size(v_keys_9_);
v___x_14_ = lean_nat_dec_lt(v_i_11_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec(v_i_11_);
v___x_15_ = lean_box(0);
return v___x_15_;
}
else
{
lean_object* v_k_x27_16_; uint8_t v___x_17_; 
v_k_x27_16_ = lean_array_fget_borrowed(v_keys_9_, v_i_11_);
v___x_17_ = l_Lean_instBEqHeadIndex_beq(v_k_12_, v_k_x27_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_i_11_, v___x_18_);
lean_dec(v_i_11_);
v_i_11_ = v___x_19_;
goto _start;
}
else
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_array_fget_borrowed(v_vals_10_, v_i_11_);
lean_dec(v_i_11_);
lean_inc(v___x_21_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_23_, lean_object* v_vals_24_, lean_object* v_i_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_23_, v_vals_24_, v_i_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec_ref(v_vals_24_);
lean_dec_ref(v_keys_23_);
return v_res_27_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; 
v___x_28_ = ((size_t)5ULL);
v___x_29_ = ((size_t)1ULL);
v___x_30_ = lean_usize_shift_left(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; 
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0);
v___x_33_ = lean_usize_sub(v___x_32_, v___x_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_34_, size_t v_x_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v_es_37_; lean_object* v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; lean_object* v_j_42_; lean_object* v___x_43_; 
v_es_37_ = lean_ctor_get(v_x_34_, 0);
v___x_38_ = lean_box(2);
v___x_39_ = ((size_t)5ULL);
v___x_40_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
v___x_41_ = lean_usize_land(v_x_35_, v___x_40_);
v_j_42_ = lean_usize_to_nat(v___x_41_);
v___x_43_ = lean_array_get_borrowed(v___x_38_, v_es_37_, v_j_42_);
lean_dec(v_j_42_);
switch(lean_obj_tag(v___x_43_))
{
case 0:
{
lean_object* v_key_44_; lean_object* v_val_45_; uint8_t v___x_46_; 
v_key_44_ = lean_ctor_get(v___x_43_, 0);
v_val_45_ = lean_ctor_get(v___x_43_, 1);
v___x_46_ = l_Lean_instBEqHeadIndex_beq(v_x_36_, v_key_44_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
lean_object* v___x_48_; 
lean_inc(v_val_45_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v_val_45_);
return v___x_48_;
}
}
case 1:
{
lean_object* v_node_49_; size_t v___x_50_; 
v_node_49_ = lean_ctor_get(v___x_43_, 0);
v___x_50_ = lean_usize_shift_right(v_x_35_, v___x_39_);
v_x_34_ = v_node_49_;
v_x_35_ = v___x_50_;
goto _start;
}
default: 
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
}
}
else
{
lean_object* v_ks_53_; lean_object* v_vs_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_ks_53_ = lean_ctor_get(v_x_34_, 0);
v_vs_54_ = lean_ctor_get(v_x_34_, 1);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_53_, v_vs_54_, v___x_55_, v_x_36_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
size_t v_x_1462__boxed_60_; lean_object* v_res_61_; 
v_x_1462__boxed_60_ = lean_unbox_usize(v_x_58_);
lean_dec(v_x_58_);
v_res_61_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_57_, v_x_1462__boxed_60_, v_x_59_);
lean_dec(v_x_59_);
lean_dec_ref(v_x_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
uint64_t v___x_64_; size_t v___x_65_; lean_object* v___x_66_; 
v___x_64_ = l_Lean_HeadIndex_hash(v_x_63_);
v___x_65_ = lean_uint64_to_usize(v___x_64_);
v___x_66_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_62_, v___x_65_, v_x_63_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_67_, v_x_68_);
lean_dec(v_x_68_);
lean_dec_ref(v_x_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(lean_object* v_e_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v_e_73_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v_x_74_);
return v___x_81_;
}
else
{
lean_object* v_key_82_; lean_object* v_value_83_; lean_object* v_tail_84_; lean_object* v___x_85_; 
lean_dec_ref(v_x_74_);
v_key_82_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_key_82_);
v_value_83_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_value_83_);
v_tail_84_ = lean_ctor_get(v_x_75_, 2);
lean_inc(v_tail_84_);
lean_dec_ref(v_x_75_);
lean_inc_ref(v_e_73_);
v___x_85_ = l_Lean_Meta_isExprDefEq(v_e_73_, v_key_82_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_100_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_100_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_100_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_100_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_box(0);
v___x_91_ = lean_unbox(v_a_86_);
lean_dec(v_a_86_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_del_object(v___x_88_);
lean_dec(v_value_83_);
v___x_92_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v_x_74_ = v___x_92_;
v_x_75_ = v_tail_84_;
goto _start;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec(v_tail_84_);
lean_dec_ref(v_e_73_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_value_83_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_90_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_96_);
v___x_98_ = v___x_88_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec(v_tail_84_);
lean_dec(v_value_83_);
lean_dec_ref(v_e_73_);
v_a_101_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_85_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_85_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___boxed(lean_object* v_e_109_, lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_109_, v_x_110_, v_x_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object* v_m_118_, lean_object* v_e_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_inc_ref(v_e_119_);
v___x_125_ = l_Lean_Expr_toHeadIndex(v_e_119_);
v___x_126_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_118_, v___x_125_);
lean_dec(v___x_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref(v_e_119_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_val_129_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_129_);
lean_dec_ref(v___x_126_);
v___x_130_ = lean_box(0);
v___x_131_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v___x_132_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_119_, v___x_131_, v_val_129_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_145_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_145_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_145_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_145_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_fst_137_; 
v_fst_137_ = lean_ctor_get(v_a_133_, 0);
lean_inc(v_fst_137_);
lean_dec(v_a_133_);
if (lean_obj_tag(v_fst_137_) == 0)
{
lean_object* v___x_139_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_130_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_130_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
else
{
lean_object* v_val_141_; lean_object* v___x_143_; 
v_val_141_ = lean_ctor_get(v_fst_137_, 0);
lean_inc(v_val_141_);
lean_dec_ref(v_fst_137_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v_val_141_);
v___x_143_ = v___x_135_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_val_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_132_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_132_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(lean_object* v_m_154_, lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_154_, v_e_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec_ref(v_m_154_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object* v_00_u03b1_162_, lean_object* v_m_163_, lean_object* v_e_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_163_, v_e_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___boxed(lean_object* v_00_u03b1_171_, lean_object* v_m_172_, lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Meta_KExprMap_find_x3f(v_00_u03b1_171_, v_m_172_, v_e_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_m_172_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(lean_object* v_00_u03b2_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_181_, v_x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(v_00_u03b2_184_, v_x_185_, v_x_186_);
lean_dec(v_x_186_);
lean_dec_ref(v_x_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_object* v_00_u03b1_188_, lean_object* v_e_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_189_, v_x_190_, v_x_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(lean_object* v_00_u03b1_198_, lean_object* v_e_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(v_00_u03b1_198_, v_e_199_, v_x_200_, v_x_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_208_, lean_object* v_x_209_, size_t v_x_210_, lean_object* v_x_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_209_, v_x_210_, v_x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
size_t v_x_1712__boxed_217_; lean_object* v_res_218_; 
v_x_1712__boxed_217_ = lean_unbox_usize(v_x_215_);
lean_dec(v_x_215_);
v_res_218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_213_, v_x_214_, v_x_1712__boxed_217_, v_x_216_);
lean_dec(v_x_216_);
lean_dec_ref(v_x_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_219_, lean_object* v_keys_220_, lean_object* v_vals_221_, lean_object* v_heq_222_, lean_object* v_i_223_, lean_object* v_k_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_220_, v_vals_221_, v_i_223_, v_k_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_heq_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_226_, v_keys_227_, v_vals_228_, v_heq_229_, v_i_230_, v_k_231_);
lean_dec(v_k_231_);
lean_dec_ref(v_vals_228_);
lean_dec_ref(v_keys_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(lean_object* v_ps_233_, lean_object* v_e_234_, lean_object* v_v_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
if (lean_obj_tag(v_ps_233_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_241_, 0, v_e_234_);
lean_ctor_set(v___x_241_, 1, v_v_235_);
lean_ctor_set(v___x_241_, 2, v_ps_233_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
else
{
lean_object* v_key_243_; lean_object* v_value_244_; lean_object* v_tail_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_282_; 
v_key_243_ = lean_ctor_get(v_ps_233_, 0);
v_value_244_ = lean_ctor_get(v_ps_233_, 1);
v_tail_245_ = lean_ctor_get(v_ps_233_, 2);
v_isSharedCheck_282_ = !lean_is_exclusive(v_ps_233_);
if (v_isSharedCheck_282_ == 0)
{
v___x_247_ = v_ps_233_;
v_isShared_248_ = v_isSharedCheck_282_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_tail_245_);
lean_inc(v_value_244_);
lean_inc(v_key_243_);
lean_dec(v_ps_233_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_282_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; 
lean_inc(v_key_243_);
lean_inc_ref(v_e_234_);
v___x_249_ = l_Lean_Meta_isExprDefEq(v_e_234_, v_key_243_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_273_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_273_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___x_254_; 
v___x_254_ = lean_unbox(v_a_250_);
lean_dec(v_a_250_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_del_object(v___x_252_);
v___x_255_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_tail_245_, v_e_234_, v_v_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_266_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_266_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_266_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_266_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 2, v_a_256_);
v___x_261_ = v___x_247_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_key_243_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_value_244_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_a_256_);
v___x_261_ = v_reuseFailAlloc_265_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_261_);
v___x_263_ = v___x_258_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
else
{
lean_del_object(v___x_247_);
lean_dec(v_value_244_);
lean_dec(v_key_243_);
return v___x_255_;
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v_value_244_);
lean_dec(v_key_243_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_v_235_);
lean_ctor_set(v___x_247_, 0, v_e_234_);
v___x_268_ = v___x_247_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_e_234_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_v_235_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_tail_245_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_268_);
v___x_270_ = v___x_252_;
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
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_del_object(v___x_247_);
lean_dec(v_tail_245_);
lean_dec(v_value_244_);
lean_dec(v_key_243_);
lean_dec(v_v_235_);
lean_dec_ref(v_e_234_);
v_a_274_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_249_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_249_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(lean_object* v_ps_283_, lean_object* v_e_284_, lean_object* v_v_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_283_, v_e_284_, v_v_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_object* v_00_u03b1_292_, lean_object* v_ps_293_, lean_object* v_e_294_, lean_object* v_v_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_293_, v_e_294_, v_v_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(lean_object* v_00_u03b1_302_, lean_object* v_ps_303_, lean_object* v_e_304_, lean_object* v_v_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(v_00_u03b1_302_, v_ps_303_, v_e_304_, v_v_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_ks_316_; lean_object* v_vs_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_341_; 
v_ks_316_ = lean_ctor_get(v_x_312_, 0);
v_vs_317_ = lean_ctor_get(v_x_312_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_341_ == 0)
{
v___x_319_ = v_x_312_;
v_isShared_320_ = v_isSharedCheck_341_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_vs_317_);
lean_inc(v_ks_316_);
lean_dec(v_x_312_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_341_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_array_get_size(v_ks_316_);
v___x_322_ = lean_nat_dec_lt(v_x_313_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
lean_dec(v_x_313_);
v___x_323_ = lean_array_push(v_ks_316_, v_x_314_);
v___x_324_ = lean_array_push(v_vs_317_, v_x_315_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_324_);
lean_ctor_set(v___x_319_, 0, v___x_323_);
v___x_326_ = v___x_319_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
else
{
lean_object* v_k_x27_328_; uint8_t v___x_329_; 
v_k_x27_328_ = lean_array_fget_borrowed(v_ks_316_, v_x_313_);
v___x_329_ = l_Lean_instBEqHeadIndex_beq(v_x_314_, v_k_x27_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_331_; 
if (v_isShared_320_ == 0)
{
v___x_331_ = v___x_319_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_ks_316_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_vs_317_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_x_313_, v___x_332_);
lean_dec(v_x_313_);
v_x_312_ = v___x_331_;
v_x_313_ = v___x_333_;
goto _start;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_array_fset(v_ks_316_, v_x_313_, v_x_314_);
v___x_337_ = lean_array_fset(v_vs_317_, v_x_313_, v_x_315_);
lean_dec(v_x_313_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_337_);
lean_ctor_set(v___x_319_, 0, v___x_336_);
v___x_339_ = v___x_319_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_342_, lean_object* v_k_343_, lean_object* v_v_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_342_, v___x_345_, v_k_343_, v_v_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(lean_object* v_x_348_, size_t v_x_349_, size_t v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v_es_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v_j_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_es_353_ = lean_ctor_get(v_x_348_, 0);
v___x_354_ = ((size_t)5ULL);
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
v___x_357_ = lean_usize_land(v_x_349_, v___x_356_);
v_j_358_ = lean_usize_to_nat(v___x_357_);
v___x_359_ = lean_array_get_size(v_es_353_);
v___x_360_ = lean_nat_dec_lt(v_j_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_dec(v_j_358_);
lean_dec(v_x_352_);
lean_dec(v_x_351_);
return v_x_348_;
}
else
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_397_; 
lean_inc_ref(v_es_353_);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_x_348_, 0);
lean_dec(v_unused_398_);
v___x_362_ = v_x_348_;
v_isShared_363_ = v_isSharedCheck_397_;
goto v_resetjp_361_;
}
else
{
lean_dec(v_x_348_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_397_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_v_364_; lean_object* v___x_365_; lean_object* v_xs_x27_366_; lean_object* v___y_368_; 
v_v_364_ = lean_array_fget(v_es_353_, v_j_358_);
v___x_365_ = lean_box(0);
v_xs_x27_366_ = lean_array_fset(v_es_353_, v_j_358_, v___x_365_);
switch(lean_obj_tag(v_v_364_))
{
case 0:
{
lean_object* v_key_373_; lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_384_; 
v_key_373_ = lean_ctor_get(v_v_364_, 0);
v_val_374_ = lean_ctor_get(v_v_364_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_v_364_);
if (v_isSharedCheck_384_ == 0)
{
v___x_376_ = v_v_364_;
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_inc(v_key_373_);
lean_dec(v_v_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_instBEqHeadIndex_beq(v_x_351_, v_key_373_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_del_object(v___x_376_);
v___x_379_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_373_, v_val_374_, v_x_351_, v_x_352_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___y_368_ = v___x_380_;
goto v___jp_367_;
}
else
{
lean_object* v___x_382_; 
lean_dec(v_val_374_);
lean_dec(v_key_373_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v_x_352_);
lean_ctor_set(v___x_376_, 0, v_x_351_);
v___x_382_ = v___x_376_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_x_351_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_x_352_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v___y_368_ = v___x_382_;
goto v___jp_367_;
}
}
}
}
case 1:
{
lean_object* v_node_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v_node_385_ = lean_ctor_get(v_v_364_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_v_364_);
if (v_isSharedCheck_395_ == 0)
{
v___x_387_ = v_v_364_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_node_385_);
lean_dec(v_v_364_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_389_ = lean_usize_shift_right(v_x_349_, v___x_354_);
v___x_390_ = lean_usize_add(v_x_350_, v___x_355_);
v___x_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_node_385_, v___x_389_, v___x_390_, v_x_351_, v_x_352_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_391_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_368_ = v___x_393_;
goto v___jp_367_;
}
}
}
default: 
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_x_351_);
lean_ctor_set(v___x_396_, 1, v_x_352_);
v___y_368_ = v___x_396_;
goto v___jp_367_;
}
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_array_fset(v_xs_x27_366_, v_j_358_, v___y_368_);
lean_dec(v_j_358_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_369_);
v___x_371_ = v___x_362_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_ks_399_; lean_object* v_vs_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_420_; 
v_ks_399_ = lean_ctor_get(v_x_348_, 0);
v_vs_400_ = lean_ctor_get(v_x_348_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_420_ == 0)
{
v___x_402_ = v_x_348_;
v_isShared_403_ = v_isSharedCheck_420_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_vs_400_);
lean_inc(v_ks_399_);
lean_dec(v_x_348_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_420_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_ks_399_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_vs_400_);
v___x_405_ = v_reuseFailAlloc_419_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v_newNode_406_; uint8_t v___y_408_; size_t v___x_414_; uint8_t v___x_415_; 
v_newNode_406_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v___x_405_, v_x_351_, v_x_352_);
v___x_414_ = ((size_t)7ULL);
v___x_415_ = lean_usize_dec_le(v___x_414_, v_x_350_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_406_);
v___x_417_ = lean_unsigned_to_nat(4u);
v___x_418_ = lean_nat_dec_lt(v___x_416_, v___x_417_);
lean_dec(v___x_416_);
v___y_408_ = v___x_418_;
goto v___jp_407_;
}
else
{
v___y_408_ = v___x_415_;
goto v___jp_407_;
}
v___jp_407_:
{
if (v___y_408_ == 0)
{
lean_object* v_ks_409_; lean_object* v_vs_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_ks_409_ = lean_ctor_get(v_newNode_406_, 0);
lean_inc_ref(v_ks_409_);
v_vs_410_ = lean_ctor_get(v_newNode_406_, 1);
lean_inc_ref(v_vs_410_);
lean_dec_ref(v_newNode_406_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
v___x_413_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_350_, v_ks_409_, v_vs_410_, v___x_411_, v___x_412_);
lean_dec_ref(v_vs_410_);
lean_dec_ref(v_ks_409_);
return v___x_413_;
}
else
{
return v_newNode_406_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_421_, lean_object* v_keys_422_, lean_object* v_vals_423_, lean_object* v_i_424_, lean_object* v_entries_425_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_array_get_size(v_keys_422_);
v___x_427_ = lean_nat_dec_lt(v_i_424_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v_i_424_);
return v_entries_425_;
}
else
{
lean_object* v_k_428_; lean_object* v_v_429_; uint64_t v___x_430_; size_t v_h_431_; size_t v___x_432_; lean_object* v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v_h_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_k_428_ = lean_array_fget_borrowed(v_keys_422_, v_i_424_);
v_v_429_ = lean_array_fget_borrowed(v_vals_423_, v_i_424_);
v___x_430_ = l_Lean_HeadIndex_hash(v_k_428_);
v_h_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = ((size_t)5ULL);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v_depth_421_, v___x_434_);
v___x_436_ = lean_usize_mul(v___x_432_, v___x_435_);
v_h_437_ = lean_usize_shift_right(v_h_431_, v___x_436_);
v___x_438_ = lean_nat_add(v_i_424_, v___x_433_);
lean_dec(v_i_424_);
lean_inc(v_v_429_);
lean_inc(v_k_428_);
v___x_439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_entries_425_, v_h_437_, v_depth_421_, v_k_428_, v_v_429_);
v_i_424_ = v___x_438_;
v_entries_425_ = v___x_439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_441_, lean_object* v_keys_442_, lean_object* v_vals_443_, lean_object* v_i_444_, lean_object* v_entries_445_){
_start:
{
size_t v_depth_boxed_446_; lean_object* v_res_447_; 
v_depth_boxed_446_ = lean_unbox_usize(v_depth_441_);
lean_dec(v_depth_441_);
v_res_447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_446_, v_keys_442_, v_vals_443_, v_i_444_, v_entries_445_);
lean_dec_ref(v_vals_443_);
lean_dec_ref(v_keys_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
size_t v_x_737__boxed_453_; size_t v_x_738__boxed_454_; lean_object* v_res_455_; 
v_x_737__boxed_453_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_x_738__boxed_454_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_res_455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_448_, v_x_737__boxed_453_, v_x_738__boxed_454_, v_x_451_, v_x_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v___x_459_ = l_Lean_HeadIndex_hash(v_x_457_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_456_, v___x_460_, v___x_461_, v_x_457_, v_x_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object* v_m_463_, lean_object* v_e_464_, lean_object* v_v_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_k_471_; lean_object* v___x_472_; 
lean_inc_ref(v_e_464_);
v_k_471_ = l_Lean_Expr_toHeadIndex(v_e_464_);
v___x_472_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_463_, v_k_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_474_, 0, v_e_464_);
lean_ctor_set(v___x_474_, 1, v_v_465_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
v___x_475_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_463_, v_k_471_, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v_val_477_; lean_object* v___x_478_; 
v_val_477_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v___x_472_);
v___x_478_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_val_477_, v_e_464_, v_v_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_463_, v_k_471_, v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_k_471_);
lean_dec_ref(v_m_463_);
v_a_488_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_478_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_478_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg___boxed(lean_object* v_m_496_, lean_object* v_e_497_, lean_object* v_v_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_496_, v_e_497_, v_v_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert(lean_object* v_00_u03b1_505_, lean_object* v_m_506_, lean_object* v_e_507_, lean_object* v_v_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_506_, v_e_507_, v_v_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___boxed(lean_object* v_00_u03b1_515_, lean_object* v_m_516_, lean_object* v_e_517_, lean_object* v_v_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_KExprMap_insert(v_00_u03b1_515_, v_m_516_, v_e_517_, v_v_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(lean_object* v_00_u03b2_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_x_526_, v_x_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_object* v_00_u03b2_530_, lean_object* v_x_531_, size_t v_x_532_, size_t v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_531_, v_x_532_, v_x_533_, v_x_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
size_t v_x_971__boxed_543_; size_t v_x_972__boxed_544_; lean_object* v_res_545_; 
v_x_971__boxed_543_ = lean_unbox_usize(v_x_539_);
lean_dec(v_x_539_);
v_x_972__boxed_544_ = lean_unbox_usize(v_x_540_);
lean_dec(v_x_540_);
v_res_545_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_537_, v_x_538_, v_x_971__boxed_543_, v_x_972__boxed_544_, v_x_541_, v_x_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_546_, lean_object* v_n_547_, lean_object* v_k_548_, lean_object* v_v_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_547_, v_k_548_, v_v_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_551_, size_t v_depth_552_, lean_object* v_keys_553_, lean_object* v_vals_554_, lean_object* v_heq_555_, lean_object* v_i_556_, lean_object* v_entries_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_552_, v_keys_553_, v_vals_554_, v_i_556_, v_entries_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_559_, lean_object* v_depth_560_, lean_object* v_keys_561_, lean_object* v_vals_562_, lean_object* v_heq_563_, lean_object* v_i_564_, lean_object* v_entries_565_){
_start:
{
size_t v_depth_boxed_566_; lean_object* v_res_567_; 
v_depth_boxed_566_ = lean_unbox_usize(v_depth_560_);
lean_dec(v_depth_560_);
v_res_567_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_559_, v_depth_boxed_566_, v_keys_561_, v_vals_562_, v_heq_563_, v_i_564_, v_entries_565_);
lean_dec_ref(v_vals_562_);
lean_dec_ref(v_keys_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_569_, v_x_570_, v_x_571_, v_x_572_);
return v___x_573_;
}
}
lean_object* runtime_initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
