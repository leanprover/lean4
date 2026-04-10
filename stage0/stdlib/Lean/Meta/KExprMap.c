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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_58_; 
v_es_37_ = lean_ctor_get(v_x_34_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_58_ == 0)
{
v___x_39_ = v_x_34_;
v_isShared_40_ = v_isSharedCheck_58_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_es_37_);
lean_dec(v_x_34_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_58_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; size_t v___x_42_; size_t v___x_43_; size_t v___x_44_; lean_object* v_j_45_; lean_object* v___x_46_; 
v___x_41_ = lean_box(2);
v___x_42_ = ((size_t)5ULL);
v___x_43_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
v___x_44_ = lean_usize_land(v_x_35_, v___x_43_);
v_j_45_ = lean_usize_to_nat(v___x_44_);
v___x_46_ = lean_array_get(v___x_41_, v_es_37_, v_j_45_);
lean_dec(v_j_45_);
lean_dec_ref(v_es_37_);
switch(lean_obj_tag(v___x_46_))
{
case 0:
{
lean_object* v_key_47_; lean_object* v_val_48_; uint8_t v___x_49_; 
v_key_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_key_47_);
v_val_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_val_48_);
lean_dec_ref(v___x_46_);
v___x_49_ = l_Lean_instBEqHeadIndex_beq(v_x_36_, v_key_47_);
lean_dec(v_key_47_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
lean_dec(v_val_48_);
lean_del_object(v___x_39_);
v___x_50_ = lean_box(0);
return v___x_50_;
}
else
{
lean_object* v___x_52_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 1);
lean_ctor_set(v___x_39_, 0, v_val_48_);
v___x_52_ = v___x_39_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_val_48_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
case 1:
{
lean_object* v_node_54_; size_t v___x_55_; 
lean_del_object(v___x_39_);
v_node_54_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_node_54_);
lean_dec_ref(v___x_46_);
v___x_55_ = lean_usize_shift_right(v_x_35_, v___x_42_);
v_x_34_ = v_node_54_;
v_x_35_ = v___x_55_;
goto _start;
}
default: 
{
lean_object* v___x_57_; 
lean_del_object(v___x_39_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
}
}
else
{
lean_object* v_ks_59_; lean_object* v_vs_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_ks_59_ = lean_ctor_get(v_x_34_, 0);
lean_inc_ref(v_ks_59_);
v_vs_60_ = lean_ctor_get(v_x_34_, 1);
lean_inc_ref(v_vs_60_);
lean_dec_ref(v_x_34_);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_59_, v_vs_60_, v___x_61_, v_x_36_);
lean_dec_ref(v_vs_60_);
lean_dec_ref(v_ks_59_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
size_t v_x_1462__boxed_66_; lean_object* v_res_67_; 
v_x_1462__boxed_66_ = lean_unbox_usize(v_x_64_);
lean_dec(v_x_64_);
v_res_67_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_63_, v_x_1462__boxed_66_, v_x_65_);
lean_dec(v_x_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint64_t v___x_70_; size_t v___x_71_; lean_object* v___x_72_; 
v___x_70_ = l_Lean_HeadIndex_hash(v_x_69_);
v___x_71_ = lean_uint64_to_usize(v___x_70_);
v___x_72_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_68_, v___x_71_, v_x_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_73_, v_x_74_);
lean_dec(v_x_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(lean_object* v_e_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v_e_79_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_x_80_);
return v___x_87_;
}
else
{
lean_object* v_key_88_; lean_object* v_value_89_; lean_object* v_tail_90_; lean_object* v___x_91_; 
lean_dec_ref(v_x_80_);
v_key_88_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_key_88_);
v_value_89_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_value_89_);
v_tail_90_ = lean_ctor_get(v_x_81_, 2);
lean_inc(v_tail_90_);
lean_dec_ref(v_x_81_);
lean_inc_ref(v_e_79_);
v___x_91_ = l_Lean_Meta_isExprDefEq(v_e_79_, v_key_88_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_106_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_106_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_box(0);
v___x_97_ = lean_unbox(v_a_92_);
lean_dec(v_a_92_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_del_object(v___x_94_);
lean_dec(v_value_89_);
v___x_98_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v_x_80_ = v___x_98_;
v_x_81_ = v_tail_90_;
goto _start;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
lean_dec(v_tail_90_);
lean_dec_ref(v_e_79_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_value_89_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_96_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_102_);
v___x_104_ = v___x_94_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec(v_tail_90_);
lean_dec(v_value_89_);
lean_dec_ref(v_e_79_);
v_a_107_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_91_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_91_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object* v_m_124_, lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_inc_ref(v_e_125_);
v___x_131_ = l_Lean_Expr_toHeadIndex(v_e_125_);
v___x_132_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_124_, v___x_131_);
lean_dec(v___x_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v_e_125_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_val_135_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_132_);
v___x_136_ = lean_box(0);
v___x_137_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v___x_138_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_125_, v___x_137_, v_val_135_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
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
lean_object* v___x_145_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_136_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_136_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
lean_object* v_val_147_; lean_object* v___x_149_; 
v_val_147_ = lean_ctor_get(v_fst_143_, 0);
lean_inc(v_val_147_);
lean_dec_ref(v_fst_143_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v_val_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_val_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_138_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_138_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(lean_object* v_m_160_, lean_object* v_e_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_160_, v_e_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object* v_00_u03b1_168_, lean_object* v_m_169_, lean_object* v_e_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_169_, v_e_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___boxed(lean_object* v_00_u03b1_177_, lean_object* v_m_178_, lean_object* v_e_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Meta_KExprMap_find_x3f(v_00_u03b1_177_, v_m_178_, v_e_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(lean_object* v_00_u03b2_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_187_, v_x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(v_00_u03b2_190_, v_x_191_, v_x_192_);
lean_dec(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_object* v_00_u03b1_194_, lean_object* v_e_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_195_, v_x_196_, v_x_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
return v___x_203_;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, size_t v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_215_, v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
size_t v_x_1724__boxed_223_; lean_object* v_res_224_; 
v_x_1724__boxed_223_ = lean_unbox_usize(v_x_221_);
lean_dec(v_x_221_);
v_res_224_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_219_, v_x_220_, v_x_1724__boxed_223_, v_x_222_);
lean_dec(v_x_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_225_, lean_object* v_keys_226_, lean_object* v_vals_227_, lean_object* v_heq_228_, lean_object* v_i_229_, lean_object* v_k_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_226_, v_vals_227_, v_i_229_, v_k_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_232_, lean_object* v_keys_233_, lean_object* v_vals_234_, lean_object* v_heq_235_, lean_object* v_i_236_, lean_object* v_k_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_232_, v_keys_233_, v_vals_234_, v_heq_235_, v_i_236_, v_k_237_);
lean_dec(v_k_237_);
lean_dec_ref(v_vals_234_);
lean_dec_ref(v_keys_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(lean_object* v_ps_239_, lean_object* v_e_240_, lean_object* v_v_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
if (lean_obj_tag(v_ps_239_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_247_, 0, v_e_240_);
lean_ctor_set(v___x_247_, 1, v_v_241_);
lean_ctor_set(v___x_247_, 2, v_ps_239_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
else
{
lean_object* v_key_249_; lean_object* v_value_250_; lean_object* v_tail_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_288_; 
v_key_249_ = lean_ctor_get(v_ps_239_, 0);
v_value_250_ = lean_ctor_get(v_ps_239_, 1);
v_tail_251_ = lean_ctor_get(v_ps_239_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v_ps_239_);
if (v_isSharedCheck_288_ == 0)
{
v___x_253_ = v_ps_239_;
v_isShared_254_ = v_isSharedCheck_288_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_tail_251_);
lean_inc(v_value_250_);
lean_inc(v_key_249_);
lean_dec(v_ps_239_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_288_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; 
lean_inc(v_key_249_);
lean_inc_ref(v_e_240_);
v___x_255_ = l_Lean_Meta_isExprDefEq(v_e_240_, v_key_249_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_279_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_279_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_279_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_279_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint8_t v___x_260_; 
v___x_260_ = lean_unbox(v_a_256_);
lean_dec(v_a_256_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_del_object(v___x_258_);
v___x_261_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_tail_251_, v_e_240_, v_v_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_272_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_272_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v_a_262_);
v___x_267_ = v___x_253_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_key_249_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_value_250_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_a_262_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_269_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_del_object(v___x_253_);
lean_dec(v_value_250_);
lean_dec(v_key_249_);
return v___x_261_;
}
}
else
{
lean_object* v___x_274_; 
lean_dec(v_value_250_);
lean_dec(v_key_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v_v_241_);
lean_ctor_set(v___x_253_, 0, v_e_240_);
v___x_274_ = v___x_253_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_e_240_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_tail_251_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_274_);
v___x_276_ = v___x_258_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_del_object(v___x_253_);
lean_dec(v_tail_251_);
lean_dec(v_value_250_);
lean_dec(v_key_249_);
lean_dec(v_v_241_);
lean_dec_ref(v_e_240_);
v_a_280_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_255_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_255_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(lean_object* v_ps_289_, lean_object* v_e_290_, lean_object* v_v_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_289_, v_e_290_, v_v_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_object* v_00_u03b1_298_, lean_object* v_ps_299_, lean_object* v_e_300_, lean_object* v_v_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_299_, v_e_300_, v_v_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(lean_object* v_00_u03b1_308_, lean_object* v_ps_309_, lean_object* v_e_310_, lean_object* v_v_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(v_00_u03b1_308_, v_ps_309_, v_e_310_, v_v_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_ks_322_; lean_object* v_vs_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_347_; 
v_ks_322_ = lean_ctor_get(v_x_318_, 0);
v_vs_323_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_347_ == 0)
{
v___x_325_ = v_x_318_;
v_isShared_326_ = v_isSharedCheck_347_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_vs_323_);
lean_inc(v_ks_322_);
lean_dec(v_x_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_347_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_ks_322_);
v___x_328_ = lean_nat_dec_lt(v_x_319_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
lean_dec(v_x_319_);
v___x_329_ = lean_array_push(v_ks_322_, v_x_320_);
v___x_330_ = lean_array_push(v_vs_323_, v_x_321_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_330_);
lean_ctor_set(v___x_325_, 0, v___x_329_);
v___x_332_ = v___x_325_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_object* v_k_x27_334_; uint8_t v___x_335_; 
v_k_x27_334_ = lean_array_fget_borrowed(v_ks_322_, v_x_319_);
v___x_335_ = l_Lean_instBEqHeadIndex_beq(v_x_320_, v_k_x27_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_337_; 
if (v_isShared_326_ == 0)
{
v___x_337_ = v___x_325_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_ks_322_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_vs_323_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_x_319_, v___x_338_);
lean_dec(v_x_319_);
v_x_318_ = v___x_337_;
v_x_319_ = v___x_339_;
goto _start;
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = lean_array_fset(v_ks_322_, v_x_319_, v_x_320_);
v___x_343_ = lean_array_fset(v_vs_323_, v_x_319_, v_x_321_);
lean_dec(v_x_319_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_343_);
lean_ctor_set(v___x_325_, 0, v___x_342_);
v___x_345_ = v___x_325_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_348_, lean_object* v_k_349_, lean_object* v_v_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_348_, v___x_351_, v_k_349_, v_v_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(lean_object* v_x_354_, size_t v_x_355_, size_t v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v_es_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v_j_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_es_359_ = lean_ctor_get(v_x_354_, 0);
v___x_360_ = ((size_t)5ULL);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
v___x_363_ = lean_usize_land(v_x_355_, v___x_362_);
v_j_364_ = lean_usize_to_nat(v___x_363_);
v___x_365_ = lean_array_get_size(v_es_359_);
v___x_366_ = lean_nat_dec_lt(v_j_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_dec(v_j_364_);
lean_dec(v_x_358_);
lean_dec(v_x_357_);
return v_x_354_;
}
else
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_403_; 
lean_inc_ref(v_es_359_);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_x_354_, 0);
lean_dec(v_unused_404_);
v___x_368_ = v_x_354_;
v_isShared_369_ = v_isSharedCheck_403_;
goto v_resetjp_367_;
}
else
{
lean_dec(v_x_354_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_403_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_v_370_; lean_object* v___x_371_; lean_object* v_xs_x27_372_; lean_object* v___y_374_; 
v_v_370_ = lean_array_fget(v_es_359_, v_j_364_);
v___x_371_ = lean_box(0);
v_xs_x27_372_ = lean_array_fset(v_es_359_, v_j_364_, v___x_371_);
switch(lean_obj_tag(v_v_370_))
{
case 0:
{
lean_object* v_key_379_; lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
v_key_379_ = lean_ctor_get(v_v_370_, 0);
v_val_380_ = lean_ctor_get(v_v_370_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_v_370_);
if (v_isSharedCheck_390_ == 0)
{
v___x_382_ = v_v_370_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_inc(v_key_379_);
lean_dec(v_v_370_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; 
v___x_384_ = l_Lean_instBEqHeadIndex_beq(v_x_357_, v_key_379_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_del_object(v___x_382_);
v___x_385_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_379_, v_val_380_, v_x_357_, v_x_358_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
v___y_374_ = v___x_386_;
goto v___jp_373_;
}
else
{
lean_object* v___x_388_; 
lean_dec(v_val_380_);
lean_dec(v_key_379_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v_x_358_);
lean_ctor_set(v___x_382_, 0, v_x_357_);
v___x_388_ = v___x_382_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_x_357_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_x_358_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v___y_374_ = v___x_388_;
goto v___jp_373_;
}
}
}
}
case 1:
{
lean_object* v_node_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_401_; 
v_node_391_ = lean_ctor_get(v_v_370_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_v_370_);
if (v_isSharedCheck_401_ == 0)
{
v___x_393_ = v_v_370_;
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_node_391_);
lean_dec(v_v_370_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_395_ = lean_usize_shift_right(v_x_355_, v___x_360_);
v___x_396_ = lean_usize_add(v_x_356_, v___x_361_);
v___x_397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_node_391_, v___x_395_, v___x_396_, v_x_357_, v_x_358_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
v___y_374_ = v___x_399_;
goto v___jp_373_;
}
}
}
default: 
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_x_357_);
lean_ctor_set(v___x_402_, 1, v_x_358_);
v___y_374_ = v___x_402_;
goto v___jp_373_;
}
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_array_fset(v_xs_x27_372_, v_j_364_, v___y_374_);
lean_dec(v_j_364_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_375_);
v___x_377_ = v___x_368_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
else
{
lean_object* v_ks_405_; lean_object* v_vs_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_426_; 
v_ks_405_ = lean_ctor_get(v_x_354_, 0);
v_vs_406_ = lean_ctor_get(v_x_354_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_426_ == 0)
{
v___x_408_ = v_x_354_;
v_isShared_409_ = v_isSharedCheck_426_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_vs_406_);
lean_inc(v_ks_405_);
lean_dec(v_x_354_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_426_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_ks_405_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_vs_406_);
v___x_411_ = v_reuseFailAlloc_425_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v_newNode_412_; uint8_t v___y_414_; size_t v___x_420_; uint8_t v___x_421_; 
v_newNode_412_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v___x_411_, v_x_357_, v_x_358_);
v___x_420_ = ((size_t)7ULL);
v___x_421_ = lean_usize_dec_le(v___x_420_, v_x_356_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_412_);
v___x_423_ = lean_unsigned_to_nat(4u);
v___x_424_ = lean_nat_dec_lt(v___x_422_, v___x_423_);
lean_dec(v___x_422_);
v___y_414_ = v___x_424_;
goto v___jp_413_;
}
else
{
v___y_414_ = v___x_421_;
goto v___jp_413_;
}
v___jp_413_:
{
if (v___y_414_ == 0)
{
lean_object* v_ks_415_; lean_object* v_vs_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_ks_415_ = lean_ctor_get(v_newNode_412_, 0);
lean_inc_ref(v_ks_415_);
v_vs_416_ = lean_ctor_get(v_newNode_412_, 1);
lean_inc_ref(v_vs_416_);
lean_dec_ref(v_newNode_412_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
v___x_419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_356_, v_ks_415_, v_vs_416_, v___x_417_, v___x_418_);
lean_dec_ref(v_vs_416_);
lean_dec_ref(v_ks_415_);
return v___x_419_;
}
else
{
return v_newNode_412_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_427_, lean_object* v_keys_428_, lean_object* v_vals_429_, lean_object* v_i_430_, lean_object* v_entries_431_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_get_size(v_keys_428_);
v___x_433_ = lean_nat_dec_lt(v_i_430_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_i_430_);
return v_entries_431_;
}
else
{
lean_object* v_k_434_; lean_object* v_v_435_; uint64_t v___x_436_; size_t v_h_437_; size_t v___x_438_; lean_object* v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v_h_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_k_434_ = lean_array_fget_borrowed(v_keys_428_, v_i_430_);
v_v_435_ = lean_array_fget_borrowed(v_vals_429_, v_i_430_);
v___x_436_ = l_Lean_HeadIndex_hash(v_k_434_);
v_h_437_ = lean_uint64_to_usize(v___x_436_);
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_sub(v_depth_427_, v___x_440_);
v___x_442_ = lean_usize_mul(v___x_438_, v___x_441_);
v_h_443_ = lean_usize_shift_right(v_h_437_, v___x_442_);
v___x_444_ = lean_nat_add(v_i_430_, v___x_439_);
lean_dec(v_i_430_);
lean_inc(v_v_435_);
lean_inc(v_k_434_);
v___x_445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_entries_431_, v_h_443_, v_depth_427_, v_k_434_, v_v_435_);
v_i_430_ = v___x_444_;
v_entries_431_ = v___x_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_447_, lean_object* v_keys_448_, lean_object* v_vals_449_, lean_object* v_i_450_, lean_object* v_entries_451_){
_start:
{
size_t v_depth_boxed_452_; lean_object* v_res_453_; 
v_depth_boxed_452_ = lean_unbox_usize(v_depth_447_);
lean_dec(v_depth_447_);
v_res_453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_452_, v_keys_448_, v_vals_449_, v_i_450_, v_entries_451_);
lean_dec_ref(v_vals_449_);
lean_dec_ref(v_keys_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
size_t v_x_737__boxed_459_; size_t v_x_738__boxed_460_; lean_object* v_res_461_; 
v_x_737__boxed_459_ = lean_unbox_usize(v_x_455_);
lean_dec(v_x_455_);
v_x_738__boxed_460_ = lean_unbox_usize(v_x_456_);
lean_dec(v_x_456_);
v_res_461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_454_, v_x_737__boxed_459_, v_x_738__boxed_460_, v_x_457_, v_x_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
uint64_t v___x_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_465_ = l_Lean_HeadIndex_hash(v_x_463_);
v___x_466_ = lean_uint64_to_usize(v___x_465_);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_462_, v___x_466_, v___x_467_, v_x_463_, v_x_464_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object* v_m_469_, lean_object* v_e_470_, lean_object* v_v_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_k_477_; lean_object* v___x_478_; 
lean_inc_ref(v_e_470_);
v_k_477_ = l_Lean_Expr_toHeadIndex(v_e_470_);
lean_inc_ref(v_m_469_);
v___x_478_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_469_, v_k_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v_e_470_);
lean_ctor_set(v___x_480_, 1, v_v_471_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
v___x_481_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_469_, v_k_477_, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v_val_483_; lean_object* v___x_484_; 
v_val_483_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_483_);
lean_dec_ref(v___x_478_);
v___x_484_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_val_483_, v_e_470_, v_v_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_493_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_469_, v_k_477_, v_a_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_k_477_);
lean_dec_ref(v_m_469_);
v_a_494_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_484_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_484_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg___boxed(lean_object* v_m_502_, lean_object* v_e_503_, lean_object* v_v_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_502_, v_e_503_, v_v_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert(lean_object* v_00_u03b1_511_, lean_object* v_m_512_, lean_object* v_e_513_, lean_object* v_v_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_512_, v_e_513_, v_v_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___boxed(lean_object* v_00_u03b1_521_, lean_object* v_m_522_, lean_object* v_e_523_, lean_object* v_v_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Meta_KExprMap_insert(v_00_u03b1_521_, v_m_522_, v_e_523_, v_v_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(lean_object* v_00_u03b2_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_x_532_, v_x_533_, v_x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_object* v_00_u03b2_536_, lean_object* v_x_537_, size_t v_x_538_, size_t v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_537_, v_x_538_, v_x_539_, v_x_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
size_t v_x_971__boxed_549_; size_t v_x_972__boxed_550_; lean_object* v_res_551_; 
v_x_971__boxed_549_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_x_972__boxed_550_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_543_, v_x_544_, v_x_971__boxed_549_, v_x_972__boxed_550_, v_x_547_, v_x_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_552_, lean_object* v_n_553_, lean_object* v_k_554_, lean_object* v_v_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_553_, v_k_554_, v_v_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_557_, size_t v_depth_558_, lean_object* v_keys_559_, lean_object* v_vals_560_, lean_object* v_heq_561_, lean_object* v_i_562_, lean_object* v_entries_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_558_, v_keys_559_, v_vals_560_, v_i_562_, v_entries_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_565_, lean_object* v_depth_566_, lean_object* v_keys_567_, lean_object* v_vals_568_, lean_object* v_heq_569_, lean_object* v_i_570_, lean_object* v_entries_571_){
_start:
{
size_t v_depth_boxed_572_; lean_object* v_res_573_; 
v_depth_boxed_572_ = lean_unbox_usize(v_depth_566_);
lean_dec(v_depth_566_);
v_res_573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_565_, v_depth_boxed_572_, v_keys_567_, v_vals_568_, v_heq_569_, v_i_570_, v_entries_571_);
lean_dec_ref(v_vals_568_);
lean_dec_ref(v_keys_567_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_575_, v_x_576_, v_x_577_, v_x_578_);
return v___x_579_;
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
