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
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_28_, size_t v_x_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_es_31_; lean_object* v___x_32_; size_t v___x_33_; size_t v___x_34_; lean_object* v_j_35_; lean_object* v___x_36_; 
v_es_31_ = lean_ctor_get(v_x_28_, 0);
v___x_32_ = lean_box(2);
v___x_33_ = ((size_t)31ULL);
v___x_34_ = lean_usize_land(v_x_29_, v___x_33_);
v_j_35_ = lean_usize_to_nat(v___x_34_);
v___x_36_ = lean_array_get_borrowed(v___x_32_, v_es_31_, v_j_35_);
lean_dec(v_j_35_);
switch(lean_obj_tag(v___x_36_))
{
case 0:
{
lean_object* v_key_37_; lean_object* v_val_38_; uint8_t v___x_39_; 
v_key_37_ = lean_ctor_get(v___x_36_, 0);
v_val_38_ = lean_ctor_get(v___x_36_, 1);
v___x_39_ = l_Lean_instBEqHeadIndex_beq(v_x_30_, v_key_37_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
lean_inc(v_val_38_);
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_val_38_);
return v___x_41_;
}
}
case 1:
{
lean_object* v_node_42_; size_t v___x_43_; size_t v___x_44_; 
v_node_42_ = lean_ctor_get(v___x_36_, 0);
v___x_43_ = ((size_t)5ULL);
v___x_44_ = lean_usize_shift_right(v_x_29_, v___x_43_);
v_x_28_ = v_node_42_;
v_x_29_ = v___x_44_;
goto _start;
}
default: 
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
}
else
{
lean_object* v_ks_47_; lean_object* v_vs_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_ks_47_ = lean_ctor_get(v_x_28_, 0);
v_vs_48_ = lean_ctor_get(v_x_28_, 1);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_47_, v_vs_48_, v___x_49_, v_x_30_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
size_t v_x_1444__boxed_54_; lean_object* v_res_55_; 
v_x_1444__boxed_54_ = lean_unbox_usize(v_x_52_);
lean_dec(v_x_52_);
v_res_55_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_51_, v_x_1444__boxed_54_, v_x_53_);
lean_dec(v_x_53_);
lean_dec_ref(v_x_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint64_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = l_Lean_HeadIndex_hash(v_x_57_);
v___x_59_ = lean_uint64_to_usize(v___x_58_);
v___x_60_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_56_, v___x_59_, v_x_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_61_, v_x_62_);
lean_dec(v_x_62_);
lean_dec_ref(v_x_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(lean_object* v_e_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v_e_67_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_x_68_);
return v___x_75_;
}
else
{
lean_object* v_key_76_; lean_object* v_value_77_; lean_object* v_tail_78_; lean_object* v___x_79_; 
lean_dec_ref(v_x_68_);
v_key_76_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_key_76_);
v_value_77_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_value_77_);
v_tail_78_ = lean_ctor_get(v_x_69_, 2);
lean_inc(v_tail_78_);
lean_dec_ref_known(v_x_69_, 3);
lean_inc_ref(v_e_67_);
v___x_79_ = l_Lean_Meta_isExprDefEq(v_e_67_, v_key_76_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_94_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_94_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_94_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_94_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_box(0);
v___x_85_ = lean_unbox(v_a_80_);
lean_dec(v_a_80_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_del_object(v___x_82_);
lean_dec(v_value_77_);
v___x_86_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v_x_68_ = v___x_86_;
v_x_69_ = v_tail_78_;
goto _start;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
lean_dec(v_tail_78_);
lean_dec_ref(v_e_67_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v_value_77_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_84_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_90_);
v___x_92_ = v___x_82_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec(v_tail_78_);
lean_dec(v_value_77_);
lean_dec_ref(v_e_67_);
v_a_95_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_79_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_79_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___boxed(lean_object* v_e_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_103_, v_x_104_, v_x_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object* v_m_112_, lean_object* v_e_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_inc_ref(v_e_113_);
v___x_119_ = l_Lean_Expr_toHeadIndex(v_e_113_);
v___x_120_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_112_, v___x_119_);
lean_dec(v___x_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec_ref(v_e_113_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_val_123_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v___x_120_, 1);
v___x_124_ = lean_box(0);
v___x_125_ = ((lean_object*)(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0));
v___x_126_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_113_, v___x_125_, v_val_123_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_139_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_139_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_139_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_139_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_fst_131_; 
v_fst_131_ = lean_ctor_get(v_a_127_, 0);
lean_inc(v_fst_131_);
lean_dec(v_a_127_);
if (lean_obj_tag(v_fst_131_) == 0)
{
lean_object* v___x_133_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_124_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_124_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v_val_135_; lean_object* v___x_137_; 
v_val_135_ = lean_ctor_get(v_fst_131_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_fst_131_, 1);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_val_135_);
v___x_137_ = v___x_129_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_val_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_126_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_126_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(lean_object* v_m_148_, lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_148_, v_e_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec_ref(v_m_148_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object* v_00_u03b1_156_, lean_object* v_m_157_, lean_object* v_e_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_m_157_, v_e_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_find_x3f___boxed(lean_object* v_00_u03b1_165_, lean_object* v_m_166_, lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_KExprMap_find_x3f(v_00_u03b1_165_, v_m_166_, v_e_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec_ref(v_m_166_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(lean_object* v_00_u03b2_174_, lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_x_175_, v_x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(v_00_u03b2_178_, v_x_179_, v_x_180_);
lean_dec(v_x_180_);
lean_dec_ref(v_x_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(lean_object* v_00_u03b1_182_, lean_object* v_e_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_183_, v_x_184_, v_x_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(lean_object* v_00_u03b1_192_, lean_object* v_e_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(v_00_u03b1_192_, v_e_193_, v_x_194_, v_x_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_202_, lean_object* v_x_203_, size_t v_x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_203_, v_x_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
size_t v_x_1688__boxed_211_; lean_object* v_res_212_; 
v_x_1688__boxed_211_ = lean_unbox_usize(v_x_209_);
lean_dec(v_x_209_);
v_res_212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_207_, v_x_208_, v_x_1688__boxed_211_, v_x_210_);
lean_dec(v_x_210_);
lean_dec_ref(v_x_208_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_213_, lean_object* v_keys_214_, lean_object* v_vals_215_, lean_object* v_heq_216_, lean_object* v_i_217_, lean_object* v_k_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_214_, v_vals_215_, v_i_217_, v_k_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_220_, lean_object* v_keys_221_, lean_object* v_vals_222_, lean_object* v_heq_223_, lean_object* v_i_224_, lean_object* v_k_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_220_, v_keys_221_, v_vals_222_, v_heq_223_, v_i_224_, v_k_225_);
lean_dec(v_k_225_);
lean_dec_ref(v_vals_222_);
lean_dec_ref(v_keys_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(lean_object* v_ps_227_, lean_object* v_e_228_, lean_object* v_v_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
if (lean_obj_tag(v_ps_227_) == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_235_, 0, v_e_228_);
lean_ctor_set(v___x_235_, 1, v_v_229_);
lean_ctor_set(v___x_235_, 2, v_ps_227_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
else
{
lean_object* v_key_237_; lean_object* v_value_238_; lean_object* v_tail_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_276_; 
v_key_237_ = lean_ctor_get(v_ps_227_, 0);
v_value_238_ = lean_ctor_get(v_ps_227_, 1);
v_tail_239_ = lean_ctor_get(v_ps_227_, 2);
v_isSharedCheck_276_ = !lean_is_exclusive(v_ps_227_);
if (v_isSharedCheck_276_ == 0)
{
v___x_241_ = v_ps_227_;
v_isShared_242_ = v_isSharedCheck_276_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_tail_239_);
lean_inc(v_value_238_);
lean_inc(v_key_237_);
lean_dec(v_ps_227_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_276_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; 
lean_inc(v_key_237_);
lean_inc_ref(v_e_228_);
v___x_243_ = l_Lean_Meta_isExprDefEq(v_e_228_, v_key_237_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_267_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_267_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; 
v___x_248_ = lean_unbox(v_a_244_);
lean_dec(v_a_244_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_del_object(v___x_246_);
v___x_249_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_tail_239_, v_e_228_, v_v_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_260_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_260_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v_a_250_);
v___x_255_ = v___x_241_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_key_237_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_value_238_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_a_250_);
v___x_255_ = v_reuseFailAlloc_259_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_255_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_del_object(v___x_241_);
lean_dec(v_value_238_);
lean_dec(v_key_237_);
return v___x_249_;
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v_value_238_);
lean_dec(v_key_237_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_v_229_);
lean_ctor_set(v___x_241_, 0, v_e_228_);
v___x_262_ = v___x_241_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_e_228_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_v_229_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_tail_239_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_262_);
v___x_264_ = v___x_246_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_del_object(v___x_241_);
lean_dec(v_tail_239_);
lean_dec(v_value_238_);
lean_dec(v_key_237_);
lean_dec(v_v_229_);
lean_dec_ref(v_e_228_);
v_a_268_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_243_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_243_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(lean_object* v_ps_277_, lean_object* v_e_278_, lean_object* v_v_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_277_, v_e_278_, v_v_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(lean_object* v_00_u03b1_286_, lean_object* v_ps_287_, lean_object* v_e_288_, lean_object* v_v_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_ps_287_, v_e_288_, v_v_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(lean_object* v_00_u03b1_296_, lean_object* v_ps_297_, lean_object* v_e_298_, lean_object* v_v_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(v_00_u03b1_296_, v_ps_297_, v_e_298_, v_v_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_ks_310_; lean_object* v_vs_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_335_; 
v_ks_310_ = lean_ctor_get(v_x_306_, 0);
v_vs_311_ = lean_ctor_get(v_x_306_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_335_ == 0)
{
v___x_313_ = v_x_306_;
v_isShared_314_ = v_isSharedCheck_335_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_vs_311_);
lean_inc(v_ks_310_);
lean_dec(v_x_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_335_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_array_get_size(v_ks_310_);
v___x_316_ = lean_nat_dec_lt(v_x_307_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_dec(v_x_307_);
v___x_317_ = lean_array_push(v_ks_310_, v_x_308_);
v___x_318_ = lean_array_push(v_vs_311_, v_x_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_318_);
lean_ctor_set(v___x_313_, 0, v___x_317_);
v___x_320_ = v___x_313_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v_k_x27_322_; uint8_t v___x_323_; 
v_k_x27_322_ = lean_array_fget_borrowed(v_ks_310_, v_x_307_);
v___x_323_ = l_Lean_instBEqHeadIndex_beq(v_x_308_, v_k_x27_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_325_; 
if (v_isShared_314_ == 0)
{
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_ks_310_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_vs_311_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v_x_307_, v___x_326_);
lean_dec(v_x_307_);
v_x_306_ = v___x_325_;
v_x_307_ = v___x_327_;
goto _start;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = lean_array_fset(v_ks_310_, v_x_307_, v_x_308_);
v___x_331_ = lean_array_fset(v_vs_311_, v_x_307_, v_x_309_);
lean_dec(v_x_307_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_331_);
lean_ctor_set(v___x_313_, 0, v___x_330_);
v___x_333_ = v___x_313_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_336_, lean_object* v_k_337_, lean_object* v_v_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_336_, v___x_339_, v_k_337_, v_v_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(lean_object* v_x_342_, size_t v_x_343_, size_t v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_es_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_j_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_es_347_ = lean_ctor_get(v_x_342_, 0);
v___x_348_ = ((size_t)31ULL);
v___x_349_ = lean_usize_land(v_x_343_, v___x_348_);
v_j_350_ = lean_usize_to_nat(v___x_349_);
v___x_351_ = lean_array_get_size(v_es_347_);
v___x_352_ = lean_nat_dec_lt(v_j_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_j_350_);
lean_dec(v_x_346_);
lean_dec(v_x_345_);
return v_x_342_;
}
else
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_391_; 
lean_inc_ref(v_es_347_);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_x_342_, 0);
lean_dec(v_unused_392_);
v___x_354_ = v_x_342_;
v_isShared_355_ = v_isSharedCheck_391_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_x_342_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_391_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_v_356_; lean_object* v___x_357_; lean_object* v_xs_x27_358_; lean_object* v___y_360_; 
v_v_356_ = lean_array_fget(v_es_347_, v_j_350_);
v___x_357_ = lean_box(0);
v_xs_x27_358_ = lean_array_fset(v_es_347_, v_j_350_, v___x_357_);
switch(lean_obj_tag(v_v_356_))
{
case 0:
{
lean_object* v_key_365_; lean_object* v_val_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_376_; 
v_key_365_ = lean_ctor_get(v_v_356_, 0);
v_val_366_ = lean_ctor_get(v_v_356_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_v_356_);
if (v_isSharedCheck_376_ == 0)
{
v___x_368_ = v_v_356_;
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_val_366_);
lean_inc(v_key_365_);
lean_dec(v_v_356_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; 
v___x_370_ = l_Lean_instBEqHeadIndex_beq(v_x_345_, v_key_365_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_del_object(v___x_368_);
v___x_371_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_365_, v_val_366_, v_x_345_, v_x_346_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___y_360_ = v___x_372_;
goto v___jp_359_;
}
else
{
lean_object* v___x_374_; 
lean_dec(v_val_366_);
lean_dec(v_key_365_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_x_346_);
lean_ctor_set(v___x_368_, 0, v_x_345_);
v___x_374_ = v___x_368_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_x_345_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_x_346_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v___y_360_ = v___x_374_;
goto v___jp_359_;
}
}
}
}
case 1:
{
lean_object* v_node_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_389_; 
v_node_377_ = lean_ctor_get(v_v_356_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_v_356_);
if (v_isSharedCheck_389_ == 0)
{
v___x_379_ = v_v_356_;
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_node_377_);
lean_dec(v_v_356_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_381_ = ((size_t)5ULL);
v___x_382_ = lean_usize_shift_right(v_x_343_, v___x_381_);
v___x_383_ = ((size_t)1ULL);
v___x_384_ = lean_usize_add(v_x_344_, v___x_383_);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_node_377_, v___x_382_, v___x_384_, v_x_345_, v_x_346_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_385_);
v___x_387_ = v___x_379_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v___y_360_ = v___x_387_;
goto v___jp_359_;
}
}
}
default: 
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_x_345_);
lean_ctor_set(v___x_390_, 1, v_x_346_);
v___y_360_ = v___x_390_;
goto v___jp_359_;
}
}
v___jp_359_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_array_fset(v_xs_x27_358_, v_j_350_, v___y_360_);
lean_dec(v_j_350_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_361_);
v___x_363_ = v___x_354_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
else
{
lean_object* v_ks_393_; lean_object* v_vs_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_414_; 
v_ks_393_ = lean_ctor_get(v_x_342_, 0);
v_vs_394_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_414_ == 0)
{
v___x_396_ = v_x_342_;
v_isShared_397_ = v_isSharedCheck_414_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_vs_394_);
lean_inc(v_ks_393_);
lean_dec(v_x_342_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_414_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_ks_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_vs_394_);
v___x_399_ = v_reuseFailAlloc_413_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v_newNode_400_; uint8_t v___y_402_; size_t v___x_408_; uint8_t v___x_409_; 
v_newNode_400_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v___x_399_, v_x_345_, v_x_346_);
v___x_408_ = ((size_t)7ULL);
v___x_409_ = lean_usize_dec_le(v___x_408_, v_x_344_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_400_);
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = lean_nat_dec_lt(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
v___y_402_ = v___x_412_;
goto v___jp_401_;
}
else
{
v___y_402_ = v___x_409_;
goto v___jp_401_;
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
lean_object* v_ks_403_; lean_object* v_vs_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_ks_403_ = lean_ctor_get(v_newNode_400_, 0);
lean_inc_ref(v_ks_403_);
v_vs_404_ = lean_ctor_get(v_newNode_400_, 1);
lean_inc_ref(v_vs_404_);
lean_dec_ref(v_newNode_400_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
v___x_407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_344_, v_ks_403_, v_vs_404_, v___x_405_, v___x_406_);
lean_dec_ref(v_vs_404_);
lean_dec_ref(v_ks_403_);
return v___x_407_;
}
else
{
return v_newNode_400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_415_, lean_object* v_keys_416_, lean_object* v_vals_417_, lean_object* v_i_418_, lean_object* v_entries_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_array_get_size(v_keys_416_);
v___x_421_ = lean_nat_dec_lt(v_i_418_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec(v_i_418_);
return v_entries_419_;
}
else
{
lean_object* v_k_422_; lean_object* v_v_423_; uint64_t v___x_424_; size_t v_h_425_; size_t v___x_426_; lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v_h_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_k_422_ = lean_array_fget_borrowed(v_keys_416_, v_i_418_);
v_v_423_ = lean_array_fget_borrowed(v_vals_417_, v_i_418_);
v___x_424_ = l_Lean_HeadIndex_hash(v_k_422_);
v_h_425_ = lean_uint64_to_usize(v___x_424_);
v___x_426_ = ((size_t)5ULL);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_sub(v_depth_415_, v___x_428_);
v___x_430_ = lean_usize_mul(v___x_426_, v___x_429_);
v_h_431_ = lean_usize_shift_right(v_h_425_, v___x_430_);
v___x_432_ = lean_nat_add(v_i_418_, v___x_427_);
lean_dec(v_i_418_);
lean_inc(v_v_423_);
lean_inc(v_k_422_);
v___x_433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_entries_419_, v_h_431_, v_depth_415_, v_k_422_, v_v_423_);
v_i_418_ = v___x_432_;
v_entries_419_ = v___x_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_435_, lean_object* v_keys_436_, lean_object* v_vals_437_, lean_object* v_i_438_, lean_object* v_entries_439_){
_start:
{
size_t v_depth_boxed_440_; lean_object* v_res_441_; 
v_depth_boxed_440_ = lean_unbox_usize(v_depth_435_);
lean_dec(v_depth_435_);
v_res_441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_440_, v_keys_436_, v_vals_437_, v_i_438_, v_entries_439_);
lean_dec_ref(v_vals_437_);
lean_dec_ref(v_keys_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
size_t v_x_729__boxed_447_; size_t v_x_730__boxed_448_; lean_object* v_res_449_; 
v_x_729__boxed_447_ = lean_unbox_usize(v_x_443_);
lean_dec(v_x_443_);
v_x_730__boxed_448_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_res_449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_442_, v_x_729__boxed_447_, v_x_730__boxed_448_, v_x_445_, v_x_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
uint64_t v___x_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
v___x_453_ = l_Lean_HeadIndex_hash(v_x_451_);
v___x_454_ = lean_uint64_to_usize(v___x_453_);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_450_, v___x_454_, v___x_455_, v_x_451_, v_x_452_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object* v_m_457_, lean_object* v_e_458_, lean_object* v_v_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_k_465_; lean_object* v___x_466_; 
lean_inc_ref(v_e_458_);
v_k_465_ = l_Lean_Expr_toHeadIndex(v_e_458_);
v___x_466_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_457_, v_k_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_468_, 0, v_e_458_);
lean_ctor_set(v___x_468_, 1, v_v_459_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
v___x_469_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_457_, v_k_465_, v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v___x_472_; 
v_val_471_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_466_, 1);
v___x_472_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(v_val_471_, v_e_458_, v_v_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_457_, v_k_465_, v_a_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_k_465_);
lean_dec_ref(v_m_457_);
v_a_482_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_472_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_472_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___redArg___boxed(lean_object* v_m_490_, lean_object* v_e_491_, lean_object* v_v_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_490_, v_e_491_, v_v_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert(lean_object* v_00_u03b1_499_, lean_object* v_m_500_, lean_object* v_e_501_, lean_object* v_v_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Meta_KExprMap_insert___redArg(v_m_500_, v_e_501_, v_v_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_KExprMap_insert___boxed(lean_object* v_00_u03b1_509_, lean_object* v_m_510_, lean_object* v_e_511_, lean_object* v_v_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_KExprMap_insert(v_00_u03b1_509_, v_m_510_, v_e_511_, v_v_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(lean_object* v_00_u03b2_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_x_520_, v_x_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(lean_object* v_00_u03b2_524_, lean_object* v_x_525_, size_t v_x_526_, size_t v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_525_, v_x_526_, v_x_527_, v_x_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
size_t v_x_963__boxed_537_; size_t v_x_964__boxed_538_; lean_object* v_res_539_; 
v_x_963__boxed_537_ = lean_unbox_usize(v_x_533_);
lean_dec(v_x_533_);
v_x_964__boxed_538_ = lean_unbox_usize(v_x_534_);
lean_dec(v_x_534_);
v_res_539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_531_, v_x_532_, v_x_963__boxed_537_, v_x_964__boxed_538_, v_x_535_, v_x_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_540_, lean_object* v_n_541_, lean_object* v_k_542_, lean_object* v_v_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_541_, v_k_542_, v_v_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_545_, size_t v_depth_546_, lean_object* v_keys_547_, lean_object* v_vals_548_, lean_object* v_heq_549_, lean_object* v_i_550_, lean_object* v_entries_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_546_, v_keys_547_, v_vals_548_, v_i_550_, v_entries_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_553_, lean_object* v_depth_554_, lean_object* v_keys_555_, lean_object* v_vals_556_, lean_object* v_heq_557_, lean_object* v_i_558_, lean_object* v_entries_559_){
_start:
{
size_t v_depth_boxed_560_; lean_object* v_res_561_; 
v_depth_boxed_560_ = lean_unbox_usize(v_depth_554_);
lean_dec(v_depth_554_);
v_res_561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_553_, v_depth_boxed_560_, v_keys_555_, v_vals_556_, v_heq_557_, v_i_558_, v_entries_559_);
lean_dec_ref(v_vals_556_);
lean_dec_ref(v_keys_555_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_563_, v_x_564_, v_x_565_, v_x_566_);
return v___x_567_;
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
