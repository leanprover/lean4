// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ExtAttr
// Imports: public import Lean.Meta.Tactic.Ext public import Lean.Meta.Tactic.Grind.Extension
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_validateExtAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid `[grind ext]`, `"};
static const lean_object* l_Lean_Meta_Grind_validateExtAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_validateExtAttr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateExtAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateExtAttr___closed__1;
static const lean_string_object l_Lean_Meta_Grind_validateExtAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "` is neither tagged with `[ext]` nor is a structure"};
static const lean_object* l_Lean_Meta_Grind_validateExtAttr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_validateExtAttr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateExtAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateExtAttr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1;
static const lean_string_object l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` is not marked with the `[grind ext]` attribute"};
static const lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(32u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v_options_26_ = lean_ctor_get(v___y_21_, 2);
v___x_27_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_26_);
v___x_29_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_29_, 0, v_env_25_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
lean_ctor_set(v___x_29_, 3, v_options_26_);
v___x_30_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_msgData_20_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___boxed(lean_object* v_msgData_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(v_msgData_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(lean_object* v_msg_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 5);
v___x_42_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(v_msg_37_, v___y_38_, v___y_39_);
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_ref_41_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_ref_41_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 1);
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v_msg_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateExtAttr___closed__1(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Meta_Grind_validateExtAttr___closed__0));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateExtAttr___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_Meta_Grind_validateExtAttr___closed__2));
v___x_62_ = l_Lean_stringToMessageData(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object* v_declName_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
lean_inc(v_declName_63_);
v___x_67_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_63_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_93_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_93_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_93_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_93_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unbox(v_a_68_);
lean_dec(v_a_68_);
v___x_73_ = lean_bool_not(v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_76_; 
lean_dec(v_declName_63_);
v___x_74_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_74_);
v___x_76_ = v___x_70_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
else
{
lean_object* v___x_78_; lean_object* v_env_79_; uint8_t v___x_80_; uint8_t v___x_81_; 
v___x_78_ = lean_st_ref_get(v_a_65_);
v_env_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc_ref(v_env_79_);
lean_dec(v___x_78_);
lean_inc(v_declName_63_);
v___x_80_ = l_Lean_isStructure(v_env_79_, v_declName_63_);
v___x_81_ = lean_bool_not(v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_declName_63_);
v___x_82_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_82_);
v___x_84_ = v___x_70_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_del_object(v___x_70_);
v___x_86_ = lean_obj_once(&l_Lean_Meta_Grind_validateExtAttr___closed__1, &l_Lean_Meta_Grind_validateExtAttr___closed__1_once, _init_l_Lean_Meta_Grind_validateExtAttr___closed__1);
v___x_87_ = 0;
v___x_88_ = l_Lean_MessageData_ofConstName(v_declName_63_, v___x_87_);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_86_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_obj_once(&l_Lean_Meta_Grind_validateExtAttr___closed__3, &l_Lean_Meta_Grind_validateExtAttr___closed__3_once, _init_l_Lean_Meta_Grind_validateExtAttr___closed__3);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v___x_91_, v_a_64_, v_a_65_);
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_declName_63_);
v_a_94_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_67_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_67_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateExtAttr___boxed(lean_object* v_declName_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(lean_object* v_00_u03b1_107_, lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v_msg_108_, v___y_109_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___boxed(lean_object* v_00_u03b1_113_, lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(v_00_u03b1_113_, v_msg_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_119_, lean_object* v_i_120_, lean_object* v_k_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_array_get_size(v_keys_119_);
v___x_123_ = lean_nat_dec_lt(v_i_120_, v___x_122_);
if (v___x_123_ == 0)
{
lean_dec(v_i_120_);
return v___x_123_;
}
else
{
lean_object* v_k_x27_124_; uint8_t v___x_125_; 
v_k_x27_124_ = lean_array_fget_borrowed(v_keys_119_, v_i_120_);
v___x_125_ = lean_name_eq(v_k_121_, v_k_x27_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_i_120_, v___x_126_);
lean_dec(v_i_120_);
v_i_120_ = v___x_127_;
goto _start;
}
else
{
lean_dec(v_i_120_);
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_129_, lean_object* v_i_130_, lean_object* v_k_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_keys_129_, v_i_130_, v_k_131_);
lean_dec(v_k_131_);
lean_dec_ref(v_keys_129_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(lean_object* v_x_134_, size_t v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v_es_137_; lean_object* v___x_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v_j_141_; lean_object* v___x_142_; 
v_es_137_ = lean_ctor_get(v_x_134_, 0);
v___x_138_ = lean_box(2);
v___x_139_ = ((size_t)31ULL);
v___x_140_ = lean_usize_land(v_x_135_, v___x_139_);
v_j_141_ = lean_usize_to_nat(v___x_140_);
v___x_142_ = lean_array_get_borrowed(v___x_138_, v_es_137_, v_j_141_);
lean_dec(v_j_141_);
switch(lean_obj_tag(v___x_142_))
{
case 0:
{
lean_object* v_key_143_; uint8_t v___x_144_; 
v_key_143_ = lean_ctor_get(v___x_142_, 0);
v___x_144_ = lean_name_eq(v_x_136_, v_key_143_);
return v___x_144_;
}
case 1:
{
lean_object* v_node_145_; size_t v___x_146_; size_t v___x_147_; 
v_node_145_ = lean_ctor_get(v___x_142_, 0);
v___x_146_ = ((size_t)5ULL);
v___x_147_ = lean_usize_shift_right(v_x_135_, v___x_146_);
v_x_134_ = v_node_145_;
v_x_135_ = v___x_147_;
goto _start;
}
default: 
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
else
{
lean_object* v_ks_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_ks_150_ = lean_ctor_get(v_x_134_, 0);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_ks_150_, v___x_151_, v_x_136_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
size_t v_x_506__boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_x_506__boxed_156_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_res_157_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_153_, v_x_506__boxed_156_, v_x_155_);
lean_dec(v_x_155_);
lean_dec_ref(v_x_153_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_159_; uint64_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1723u);
v___x_160_ = lean_uint64_of_nat(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint64_t v___y_164_; 
if (lean_obj_tag(v_x_162_) == 0)
{
uint64_t v___x_167_; 
v___x_167_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0);
v___y_164_ = v___x_167_;
goto v___jp_163_;
}
else
{
uint64_t v_hash_168_; 
v_hash_168_ = lean_ctor_get_uint64(v_x_162_, sizeof(void*)*2);
v___y_164_ = v_hash_168_;
goto v___jp_163_;
}
v___jp_163_:
{
size_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_uint64_to_usize(v___y_164_);
v___x_166_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_161_, v___x_165_, v_x_162_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___boxed(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_x_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec_ref(v_x_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(lean_object* v_xs_173_, lean_object* v_v_174_, lean_object* v_i_175_){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_array_get_size(v_xs_173_);
v___x_177_ = lean_nat_dec_lt(v_i_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v_i_175_);
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_array_fget_borrowed(v_xs_173_, v_i_175_);
v___x_180_ = lean_name_eq(v___x_179_, v_v_174_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_175_, v___x_181_);
lean_dec(v_i_175_);
v_i_175_ = v___x_182_;
goto _start;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_i_175_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_xs_185_, lean_object* v_v_186_, lean_object* v_i_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(v_xs_185_, v_v_186_, v_i_187_);
lean_dec(v_v_186_);
lean_dec_ref(v_xs_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(lean_object* v_xs_189_, lean_object* v_v_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(v_xs_189_, v_v_190_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4___boxed(lean_object* v_xs_193_, lean_object* v_v_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(v_xs_193_, v_v_194_);
lean_dec(v_v_194_);
lean_dec_ref(v_xs_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(lean_object* v_x_196_, size_t v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_es_199_; lean_object* v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v_j_203_; lean_object* v_entry_204_; 
v_es_199_ = lean_ctor_get(v_x_196_, 0);
v___x_200_ = lean_box(2);
v___x_201_ = ((size_t)31ULL);
v___x_202_ = lean_usize_land(v_x_197_, v___x_201_);
v_j_203_ = lean_usize_to_nat(v___x_202_);
v_entry_204_ = lean_array_get(v___x_200_, v_es_199_, v_j_203_);
switch(lean_obj_tag(v_entry_204_))
{
case 0:
{
lean_object* v_key_205_; uint8_t v___x_206_; 
v_key_205_ = lean_ctor_get(v_entry_204_, 0);
lean_inc(v_key_205_);
lean_dec_ref_known(v_entry_204_, 2);
v___x_206_ = lean_name_eq(v_x_198_, v_key_205_);
lean_dec(v_key_205_);
if (v___x_206_ == 0)
{
lean_dec(v_j_203_);
return v_x_196_;
}
else
{
lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_214_; 
lean_inc_ref(v_es_199_);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_x_196_, 0);
lean_dec(v_unused_215_);
v___x_208_ = v_x_196_;
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
else
{
lean_dec(v_x_196_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_array_set(v_es_199_, v_j_203_, v___x_200_);
lean_dec(v_j_203_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_210_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
case 1:
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_250_; 
lean_inc_ref(v_es_199_);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_x_196_, 0);
lean_dec(v_unused_251_);
v___x_217_ = v_x_196_;
v_isShared_218_ = v_isSharedCheck_250_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_x_196_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_250_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_node_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_249_; 
v_node_219_ = lean_ctor_get(v_entry_204_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_entry_204_);
if (v_isSharedCheck_249_ == 0)
{
v___x_221_ = v_entry_204_;
v_isShared_222_ = v_isSharedCheck_249_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_node_219_);
lean_dec(v_entry_204_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_249_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
size_t v___x_223_; lean_object* v_entries_224_; size_t v___x_225_; lean_object* v_newNode_226_; lean_object* v___x_227_; 
v___x_223_ = ((size_t)5ULL);
v_entries_224_ = lean_array_set(v_es_199_, v_j_203_, v___x_200_);
v___x_225_ = lean_usize_shift_right(v_x_197_, v___x_223_);
v_newNode_226_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_node_219_, v___x_225_, v_x_198_);
lean_inc_ref(v_newNode_226_);
v___x_227_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_229_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_newNode_226_);
v___x_229_ = v___x_221_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_newNode_226_);
v___x_229_ = v_reuseFailAlloc_234_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_array_set(v_entries_224_, v_j_203_, v___x_229_);
lean_dec(v_j_203_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_230_);
v___x_232_ = v___x_217_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_object* v_val_235_; lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v_newNode_226_);
lean_del_object(v___x_221_);
v_val_235_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_227_, 1);
v_fst_236_ = lean_ctor_get(v_val_235_, 0);
v_snd_237_ = lean_ctor_get(v_val_235_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_val_235_);
if (v_isSharedCheck_248_ == 0)
{
v___x_239_ = v_val_235_;
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snd_237_);
lean_inc(v_fst_236_);
lean_dec(v_val_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_snd_237_);
v___x_242_ = v_reuseFailAlloc_247_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_array_set(v_entries_224_, v_j_203_, v___x_242_);
lean_dec(v_j_203_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_243_);
v___x_245_ = v___x_217_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_203_);
return v_x_196_;
}
}
}
else
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_267_; 
v_ks_252_ = lean_ctor_get(v_x_196_, 0);
v_vs_253_ = lean_ctor_get(v_x_196_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_267_ == 0)
{
v___x_255_ = v_x_196_;
v_isShared_256_ = v_isSharedCheck_267_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_inc(v_ks_252_);
lean_dec(v_x_196_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_267_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; 
v___x_257_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(v_ks_252_, v_x_198_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_259_; 
if (v_isShared_256_ == 0)
{
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_ks_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_vs_253_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v_val_261_; lean_object* v_keys_x27_262_; lean_object* v_vals_x27_263_; lean_object* v___x_265_; 
v_val_261_ = lean_ctor_get(v___x_257_, 0);
lean_inc_n(v_val_261_, 2);
lean_dec_ref_known(v___x_257_, 1);
v_keys_x27_262_ = l_Array_eraseIdx___redArg(v_ks_252_, v_val_261_);
v_vals_x27_263_ = l_Array_eraseIdx___redArg(v_vs_253_, v_val_261_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v_vals_x27_263_);
lean_ctor_set(v___x_255_, 0, v_keys_x27_262_);
v___x_265_ = v___x_255_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_keys_x27_262_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_vals_x27_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg___boxed(lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
size_t v_x_591__boxed_271_; lean_object* v_res_272_; 
v_x_591__boxed_271_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_res_272_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_268_, v_x_591__boxed_271_, v_x_270_);
lean_dec(v_x_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint64_t v___y_276_; 
if (lean_obj_tag(v_x_274_) == 0)
{
uint64_t v___x_279_; 
v___x_279_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0);
v___y_276_ = v___x_279_;
goto v___jp_275_;
}
else
{
uint64_t v_hash_280_; 
v_hash_280_ = lean_ctor_get_uint64(v_x_274_, sizeof(void*)*2);
v___y_276_ = v_hash_280_;
goto v___jp_275_;
}
v___jp_275_:
{
size_t v_h_277_; lean_object* v___x_278_; 
v_h_277_ = lean_uint64_to_usize(v___y_276_);
v___x_278_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_273_, v_h_277_, v_x_274_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg___boxed(lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_x_281_, v_x_282_);
lean_dec(v_x_282_);
return v_res_283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object* v_s_290_, lean_object* v_declName_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_s_290_, v_declName_291_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref(v_s_290_);
v___x_296_ = lean_obj_once(&l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1, &l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1_once, _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1);
v___x_297_ = l_Lean_MessageData_ofConstName(v_declName_291_, v___x_295_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3, &l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3_once, _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v___x_300_, v_a_292_, v_a_293_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_s_290_, v_declName_291_);
lean_dec(v_declName_291_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___boxed(lean_object* v_s_304_, lean_object* v_declName_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_s_304_, v_declName_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(lean_object* v_00_u03b2_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_x_311_, v_x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___boxed(lean_object* v_00_u03b2_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(v_00_u03b2_314_, v_x_315_, v_x_316_);
lean_dec(v_x_316_);
lean_dec_ref(v_x_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(lean_object* v_00_u03b2_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_x_320_, v_x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___boxed(lean_object* v_00_u03b2_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(v_00_u03b2_323_, v_x_324_, v_x_325_);
lean_dec(v_x_325_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(lean_object* v_00_u03b2_327_, lean_object* v_x_328_, size_t v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_328_, v_x_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
size_t v_x_799__boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_x_799__boxed_336_ = lean_unbox_usize(v_x_334_);
lean_dec(v_x_334_);
v_res_337_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(v_00_u03b2_332_, v_x_333_, v_x_799__boxed_336_, v_x_335_);
lean_dec(v_x_335_);
lean_dec_ref(v_x_333_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(lean_object* v_00_u03b2_339_, lean_object* v_x_340_, size_t v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_340_, v_x_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
size_t v_x_810__boxed_348_; lean_object* v_res_349_; 
v_x_810__boxed_348_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_res_349_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(v_00_u03b2_344_, v_x_345_, v_x_810__boxed_348_, v_x_347_);
lean_dec(v_x_347_);
return v_res_349_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_350_, lean_object* v_keys_351_, lean_object* v_vals_352_, lean_object* v_heq_353_, lean_object* v_i_354_, lean_object* v_k_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_keys_351_, v_i_354_, v_k_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_357_, lean_object* v_keys_358_, lean_object* v_vals_359_, lean_object* v_heq_360_, lean_object* v_i_361_, lean_object* v_k_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(v_00_u03b2_357_, v_keys_358_, v_vals_359_, v_heq_360_, v_i_361_, v_k_362_);
lean_dec(v_k_362_);
lean_dec_ref(v_vals_359_);
lean_dec_ref(v_keys_358_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Ext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Ext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
}
#ifdef __cplusplus
}
#endif
