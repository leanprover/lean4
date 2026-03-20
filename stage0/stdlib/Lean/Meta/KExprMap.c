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
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedKExprMap_default(lean_object* v_a_4_){
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
size_t v_x_1444__boxed_66_; lean_object* v_res_67_; 
v_x_1444__boxed_66_ = lean_unbox_usize(v_x_64_);
lean_dec(v_x_64_);
v_res_67_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_63_, v_x_1444__boxed_66_, v_x_65_);
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
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
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
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
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
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
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
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
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
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object* v_m_124_, lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_inc_ref(v_e_125_);
v___x_134_ = l_Lean_Expr_toHeadIndex(v_e_125_);
v___x_135_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_124_, v___x_134_);
lean_dec(v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec_ref(v_e_125_);
goto v___jp_131_;
}
else
{
lean_object* v_val_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_val_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_val_136_);
lean_dec_ref(v___x_135_);
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
lean_dec_ref(v_fst_143_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(lean_object* v_m_157_, lean_object* v_e_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_157_, v_e_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object* v_00_u03b1_165_, lean_object* v_m_166_, lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_166_, v_e_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___boxed(lean_object* v_00_u03b1_174_, lean_object* v_m_175_, lean_object* v_e_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_KExprMap_find_x3f(v_00_u03b1_174_, v_m_175_, v_e_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(lean_object* v_00_u03b2_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_184_, v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(v_00_u03b2_187_, v_x_188_, v_x_189_);
lean_dec(v_x_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_object* v_00_u03b1_191_, lean_object* v_e_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_192_, v_x_193_, v_x_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(lean_object* v_00_u03b1_201_, lean_object* v_e_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(v_00_u03b1_201_, v_e_202_, v_x_203_, v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_211_, lean_object* v_x_212_, size_t v_x_213_, lean_object* v_x_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_212_, v_x_213_, v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_216_, lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
size_t v_x_1725__boxed_220_; lean_object* v_res_221_; 
v_x_1725__boxed_220_ = lean_unbox_usize(v_x_218_);
lean_dec(v_x_218_);
v_res_221_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_216_, v_x_217_, v_x_1725__boxed_220_, v_x_219_);
lean_dec(v_x_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_222_, lean_object* v_keys_223_, lean_object* v_vals_224_, lean_object* v_heq_225_, lean_object* v_i_226_, lean_object* v_k_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_223_, v_vals_224_, v_i_226_, v_k_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_229_, lean_object* v_keys_230_, lean_object* v_vals_231_, lean_object* v_heq_232_, lean_object* v_i_233_, lean_object* v_k_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_229_, v_keys_230_, v_vals_231_, v_heq_232_, v_i_233_, v_k_234_);
lean_dec(v_k_234_);
lean_dec_ref(v_vals_231_);
lean_dec_ref(v_keys_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(lean_object* v_ps_236_, lean_object* v_e_237_, lean_object* v_v_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
if (lean_obj_tag(v_ps_236_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
v___x_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_244_, 0, v_e_237_);
lean_ctor_set(v___x_244_, 1, v_v_238_);
lean_ctor_set(v___x_244_, 2, v_ps_236_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v_key_246_; lean_object* v_value_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_285_; 
v_key_246_ = lean_ctor_get(v_ps_236_, 0);
v_value_247_ = lean_ctor_get(v_ps_236_, 1);
v_tail_248_ = lean_ctor_get(v_ps_236_, 2);
v_isSharedCheck_285_ = !lean_is_exclusive(v_ps_236_);
if (v_isSharedCheck_285_ == 0)
{
v___x_250_ = v_ps_236_;
v_isShared_251_ = v_isSharedCheck_285_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_value_247_);
lean_inc(v_key_246_);
lean_dec(v_ps_236_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_285_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; 
lean_inc(v_a_242_);
lean_inc_ref(v_a_241_);
lean_inc(v_a_240_);
lean_inc_ref(v_a_239_);
lean_inc(v_key_246_);
lean_inc_ref(v_e_237_);
v___x_252_ = l_Lean_Meta_isExprDefEq(v_e_237_, v_key_246_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_276_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_276_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_276_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_276_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; 
v___x_257_ = lean_unbox(v_a_253_);
lean_dec(v_a_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_del_object(v___x_255_);
v___x_258_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_tail_248_, v_e_237_, v_v_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 2, v_a_259_);
v___x_264_ = v___x_250_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_key_246_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_value_247_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_a_259_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_del_object(v___x_250_);
lean_dec(v_value_247_);
lean_dec(v_key_246_);
return v___x_258_;
}
}
else
{
lean_object* v___x_271_; 
lean_dec(v_value_247_);
lean_dec(v_key_246_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_v_238_);
lean_ctor_set(v___x_250_, 0, v_e_237_);
v___x_271_ = v___x_250_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_e_237_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_tail_248_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_271_);
v___x_273_ = v___x_255_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_del_object(v___x_250_);
lean_dec(v_tail_248_);
lean_dec(v_value_247_);
lean_dec(v_key_246_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_v_238_);
lean_dec_ref(v_e_237_);
v_a_277_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_252_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_252_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(lean_object* v_ps_286_, lean_object* v_e_287_, lean_object* v_v_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_286_, v_e_287_, v_v_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_object* v_00_u03b1_295_, lean_object* v_ps_296_, lean_object* v_e_297_, lean_object* v_v_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_296_, v_e_297_, v_v_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(lean_object* v_00_u03b1_305_, lean_object* v_ps_306_, lean_object* v_e_307_, lean_object* v_v_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(v_00_u03b1_305_, v_ps_306_, v_e_307_, v_v_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_ks_319_; lean_object* v_vs_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_344_; 
v_ks_319_ = lean_ctor_get(v_x_315_, 0);
v_vs_320_ = lean_ctor_get(v_x_315_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_344_ == 0)
{
v___x_322_ = v_x_315_;
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_vs_320_);
lean_inc(v_ks_319_);
lean_dec(v_x_315_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_get_size(v_ks_319_);
v___x_325_ = lean_nat_dec_lt(v_x_316_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec(v_x_316_);
v___x_326_ = lean_array_push(v_ks_319_, v_x_317_);
v___x_327_ = lean_array_push(v_vs_320_, v_x_318_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_327_);
lean_ctor_set(v___x_322_, 0, v___x_326_);
v___x_329_ = v___x_322_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
else
{
lean_object* v_k_x27_331_; uint8_t v___x_332_; 
v_k_x27_331_ = lean_array_fget_borrowed(v_ks_319_, v_x_316_);
v___x_332_ = l_Lean_instBEqHeadIndex_beq(v_x_317_, v_k_x27_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_334_; 
if (v_isShared_323_ == 0)
{
v___x_334_ = v___x_322_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_ks_319_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_vs_320_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_x_316_, v___x_335_);
lean_dec(v_x_316_);
v_x_315_ = v___x_334_;
v_x_316_ = v___x_336_;
goto _start;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = lean_array_fset(v_ks_319_, v_x_316_, v_x_317_);
v___x_340_ = lean_array_fset(v_vs_320_, v_x_316_, v_x_318_);
lean_dec(v_x_316_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_340_);
lean_ctor_set(v___x_322_, 0, v___x_339_);
v___x_342_ = v___x_322_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_345_, lean_object* v_k_346_, lean_object* v_v_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_345_, v___x_348_, v_k_346_, v_v_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(lean_object* v_x_351_, size_t v_x_352_, size_t v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v_es_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v_j_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_es_356_ = lean_ctor_get(v_x_351_, 0);
v___x_357_ = ((size_t)5ULL);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
v___x_360_ = lean_usize_land(v_x_352_, v___x_359_);
v_j_361_ = lean_usize_to_nat(v___x_360_);
v___x_362_ = lean_array_get_size(v_es_356_);
v___x_363_ = lean_nat_dec_lt(v_j_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v_j_361_);
lean_dec(v_x_355_);
lean_dec(v_x_354_);
return v_x_351_;
}
else
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_400_; 
lean_inc_ref(v_es_356_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_x_351_, 0);
lean_dec(v_unused_401_);
v___x_365_ = v_x_351_;
v_isShared_366_ = v_isSharedCheck_400_;
goto v_resetjp_364_;
}
else
{
lean_dec(v_x_351_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_400_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_v_367_; lean_object* v___x_368_; lean_object* v_xs_x27_369_; lean_object* v___y_371_; 
v_v_367_ = lean_array_fget(v_es_356_, v_j_361_);
v___x_368_ = lean_box(0);
v_xs_x27_369_ = lean_array_fset(v_es_356_, v_j_361_, v___x_368_);
switch(lean_obj_tag(v_v_367_))
{
case 0:
{
lean_object* v_key_376_; lean_object* v_val_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_387_; 
v_key_376_ = lean_ctor_get(v_v_367_, 0);
v_val_377_ = lean_ctor_get(v_v_367_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_v_367_);
if (v_isSharedCheck_387_ == 0)
{
v___x_379_ = v_v_367_;
v_isShared_380_ = v_isSharedCheck_387_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_val_377_);
lean_inc(v_key_376_);
lean_dec(v_v_367_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_387_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
uint8_t v___x_381_; 
v___x_381_ = l_Lean_instBEqHeadIndex_beq(v_x_354_, v_key_376_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_del_object(v___x_379_);
v___x_382_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_376_, v_val_377_, v_x_354_, v_x_355_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___y_371_ = v___x_383_;
goto v___jp_370_;
}
else
{
lean_object* v___x_385_; 
lean_dec(v_val_377_);
lean_dec(v_key_376_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v_x_355_);
lean_ctor_set(v___x_379_, 0, v_x_354_);
v___x_385_ = v___x_379_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_x_354_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_x_355_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
v___y_371_ = v___x_385_;
goto v___jp_370_;
}
}
}
}
case 1:
{
lean_object* v_node_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_398_; 
v_node_388_ = lean_ctor_get(v_v_367_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_v_367_);
if (v_isSharedCheck_398_ == 0)
{
v___x_390_ = v_v_367_;
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_node_388_);
lean_dec(v_v_367_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_392_ = lean_usize_shift_right(v_x_352_, v___x_357_);
v___x_393_ = lean_usize_add(v_x_353_, v___x_358_);
v___x_394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_node_388_, v___x_392_, v___x_393_, v_x_354_, v_x_355_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_394_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
v___y_371_ = v___x_396_;
goto v___jp_370_;
}
}
}
default: 
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_x_354_);
lean_ctor_set(v___x_399_, 1, v_x_355_);
v___y_371_ = v___x_399_;
goto v___jp_370_;
}
}
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_array_fset(v_xs_x27_369_, v_j_361_, v___y_371_);
lean_dec(v_j_361_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_372_);
v___x_374_ = v___x_365_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
else
{
lean_object* v_ks_402_; lean_object* v_vs_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_423_; 
v_ks_402_ = lean_ctor_get(v_x_351_, 0);
v_vs_403_ = lean_ctor_get(v_x_351_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_423_ == 0)
{
v___x_405_ = v_x_351_;
v_isShared_406_ = v_isSharedCheck_423_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_vs_403_);
lean_inc(v_ks_402_);
lean_dec(v_x_351_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_423_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_ks_402_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_vs_403_);
v___x_408_ = v_reuseFailAlloc_422_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v_newNode_409_; uint8_t v___y_411_; size_t v___x_417_; uint8_t v___x_418_; 
v_newNode_409_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v___x_408_, v_x_354_, v_x_355_);
v___x_417_ = ((size_t)7ULL);
v___x_418_ = lean_usize_dec_le(v___x_417_, v_x_353_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_419_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_409_);
v___x_420_ = lean_unsigned_to_nat(4u);
v___x_421_ = lean_nat_dec_lt(v___x_419_, v___x_420_);
lean_dec(v___x_419_);
v___y_411_ = v___x_421_;
goto v___jp_410_;
}
else
{
v___y_411_ = v___x_418_;
goto v___jp_410_;
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
lean_object* v_ks_412_; lean_object* v_vs_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_ks_412_ = lean_ctor_get(v_newNode_409_, 0);
lean_inc_ref(v_ks_412_);
v_vs_413_ = lean_ctor_get(v_newNode_409_, 1);
lean_inc_ref(v_vs_413_);
lean_dec_ref(v_newNode_409_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
v___x_416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_353_, v_ks_412_, v_vs_413_, v___x_414_, v___x_415_);
lean_dec_ref(v_vs_413_);
lean_dec_ref(v_ks_412_);
return v___x_416_;
}
else
{
return v_newNode_409_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_424_, lean_object* v_keys_425_, lean_object* v_vals_426_, lean_object* v_i_427_, lean_object* v_entries_428_){
_start:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_array_get_size(v_keys_425_);
v___x_430_ = lean_nat_dec_lt(v_i_427_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec(v_i_427_);
return v_entries_428_;
}
else
{
lean_object* v_k_431_; lean_object* v_v_432_; uint64_t v___x_433_; size_t v_h_434_; size_t v___x_435_; lean_object* v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v_h_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_k_431_ = lean_array_fget_borrowed(v_keys_425_, v_i_427_);
v_v_432_ = lean_array_fget_borrowed(v_vals_426_, v_i_427_);
v___x_433_ = l_Lean_HeadIndex_hash(v_k_431_);
v_h_434_ = lean_uint64_to_usize(v___x_433_);
v___x_435_ = ((size_t)5ULL);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_sub(v_depth_424_, v___x_437_);
v___x_439_ = lean_usize_mul(v___x_435_, v___x_438_);
v_h_440_ = lean_usize_shift_right(v_h_434_, v___x_439_);
v___x_441_ = lean_nat_add(v_i_427_, v___x_436_);
lean_dec(v_i_427_);
lean_inc(v_v_432_);
lean_inc(v_k_431_);
v___x_442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_entries_428_, v_h_440_, v_depth_424_, v_k_431_, v_v_432_);
v_i_427_ = v___x_441_;
v_entries_428_ = v___x_442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_444_, lean_object* v_keys_445_, lean_object* v_vals_446_, lean_object* v_i_447_, lean_object* v_entries_448_){
_start:
{
size_t v_depth_boxed_449_; lean_object* v_res_450_; 
v_depth_boxed_449_ = lean_unbox_usize(v_depth_444_);
lean_dec(v_depth_444_);
v_res_450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_449_, v_keys_445_, v_vals_446_, v_i_447_, v_entries_448_);
lean_dec_ref(v_vals_446_);
lean_dec_ref(v_keys_445_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
size_t v_x_807__boxed_456_; size_t v_x_808__boxed_457_; lean_object* v_res_458_; 
v_x_807__boxed_456_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_x_808__boxed_457_ = lean_unbox_usize(v_x_453_);
lean_dec(v_x_453_);
v_res_458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_451_, v_x_807__boxed_456_, v_x_808__boxed_457_, v_x_454_, v_x_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint64_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_462_ = l_Lean_HeadIndex_hash(v_x_460_);
v___x_463_ = lean_uint64_to_usize(v___x_462_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_459_, v___x_463_, v___x_464_, v_x_460_, v_x_461_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object* v_m_466_, lean_object* v_e_467_, lean_object* v_v_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_k_474_; lean_object* v___x_475_; 
lean_inc_ref(v_e_467_);
v_k_474_ = l_Lean_Expr_toHeadIndex(v_e_467_);
lean_inc_ref(v_m_466_);
v___x_475_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_466_, v_k_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_477_, 0, v_e_467_);
lean_ctor_set(v___x_477_, 1, v_v_468_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
v___x_478_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_466_, v_k_474_, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; 
v_val_480_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_val_480_);
lean_dec_ref(v___x_475_);
v___x_481_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_val_480_, v_e_467_, v_v_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_490_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_466_, v_k_474_, v_a_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_k_474_);
lean_dec_ref(v_m_466_);
v_a_491_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_481_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg___boxed(lean_object* v_m_499_, lean_object* v_e_500_, lean_object* v_v_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_499_, v_e_500_, v_v_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert(lean_object* v_00_u03b1_508_, lean_object* v_m_509_, lean_object* v_e_510_, lean_object* v_v_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_509_, v_e_510_, v_v_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___boxed(lean_object* v_00_u03b1_518_, lean_object* v_m_519_, lean_object* v_e_520_, lean_object* v_v_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_KExprMap_insert(v_00_u03b1_518_, v_m_519_, v_e_520_, v_v_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(lean_object* v_00_u03b2_528_, lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_x_529_, v_x_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_object* v_00_u03b2_533_, lean_object* v_x_534_, size_t v_x_535_, size_t v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_534_, v_x_535_, v_x_536_, v_x_537_, v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
size_t v_x_1065__boxed_546_; size_t v_x_1066__boxed_547_; lean_object* v_res_548_; 
v_x_1065__boxed_546_ = lean_unbox_usize(v_x_542_);
lean_dec(v_x_542_);
v_x_1066__boxed_547_ = lean_unbox_usize(v_x_543_);
lean_dec(v_x_543_);
v_res_548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_540_, v_x_541_, v_x_1065__boxed_546_, v_x_1066__boxed_547_, v_x_544_, v_x_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_549_, lean_object* v_n_550_, lean_object* v_k_551_, lean_object* v_v_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_550_, v_k_551_, v_v_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_554_, size_t v_depth_555_, lean_object* v_keys_556_, lean_object* v_vals_557_, lean_object* v_heq_558_, lean_object* v_i_559_, lean_object* v_entries_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_555_, v_keys_556_, v_vals_557_, v_i_559_, v_entries_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_562_, lean_object* v_depth_563_, lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_heq_566_, lean_object* v_i_567_, lean_object* v_entries_568_){
_start:
{
size_t v_depth_boxed_569_; lean_object* v_res_570_; 
v_depth_boxed_569_ = lean_unbox_usize(v_depth_563_);
lean_dec(v_depth_563_);
v_res_570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_562_, v_depth_boxed_569_, v_keys_564_, v_vals_565_, v_heq_566_, v_i_567_, v_entries_568_);
lean_dec_ref(v_vals_565_);
lean_dec_ref(v_keys_564_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_572_, v_x_573_, v_x_574_, v_x_575_);
return v___x_576_;
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
