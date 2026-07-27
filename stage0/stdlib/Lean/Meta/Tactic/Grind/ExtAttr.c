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
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_90_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_90_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_90_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_90_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = lean_unbox(v_a_68_);
lean_dec(v_a_68_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v_env_74_; uint8_t v___x_75_; 
v___x_73_ = lean_st_ref_get(v_a_65_);
v_env_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_env_74_);
lean_dec(v___x_73_);
lean_inc(v_declName_63_);
v___x_75_ = l_Lean_isStructure(v_env_74_, v_declName_63_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_del_object(v___x_70_);
v___x_76_ = lean_obj_once(&l_Lean_Meta_Grind_validateExtAttr___closed__1, &l_Lean_Meta_Grind_validateExtAttr___closed__1_once, _init_l_Lean_Meta_Grind_validateExtAttr___closed__1);
v___x_77_ = l_Lean_MessageData_ofConstName(v_declName_63_, v___x_75_);
v___x_78_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_obj_once(&l_Lean_Meta_Grind_validateExtAttr___closed__3, &l_Lean_Meta_Grind_validateExtAttr___closed__3_once, _init_l_Lean_Meta_Grind_validateExtAttr___closed__3);
v___x_80_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v___x_80_, v_a_64_, v_a_65_);
return v___x_81_;
}
else
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
}
else
{
lean_object* v___x_86_; lean_object* v___x_88_; 
lean_dec(v_declName_63_);
v___x_86_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_86_);
v___x_88_ = v___x_70_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v_declName_63_);
v_a_91_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_67_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_67_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateExtAttr___boxed(lean_object* v_declName_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_99_, v_a_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(lean_object* v_00_u03b1_104_, lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v_msg_105_, v___y_106_, v___y_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___boxed(lean_object* v_00_u03b1_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(v_00_u03b1_110_, v_msg_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_116_, lean_object* v_i_117_, lean_object* v_k_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_array_get_size(v_keys_116_);
v___x_120_ = lean_nat_dec_lt(v_i_117_, v___x_119_);
if (v___x_120_ == 0)
{
lean_dec(v_i_117_);
return v___x_120_;
}
else
{
lean_object* v_k_x27_121_; uint8_t v___x_122_; 
v_k_x27_121_ = lean_array_fget_borrowed(v_keys_116_, v_i_117_);
v___x_122_ = lean_name_eq(v_k_118_, v_k_x27_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_i_117_, v___x_123_);
lean_dec(v_i_117_);
v_i_117_ = v___x_124_;
goto _start;
}
else
{
lean_dec(v_i_117_);
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_126_, lean_object* v_i_127_, lean_object* v_k_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_keys_126_, v_i_127_, v_k_128_);
lean_dec(v_k_128_);
lean_dec_ref(v_keys_126_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(lean_object* v_x_131_, size_t v_x_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v_es_134_; lean_object* v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_j_138_; lean_object* v___x_139_; 
v_es_134_ = lean_ctor_get(v_x_131_, 0);
v___x_135_ = lean_box(2);
v___x_136_ = ((size_t)31ULL);
v___x_137_ = lean_usize_land(v_x_132_, v___x_136_);
v_j_138_ = lean_usize_to_nat(v___x_137_);
v___x_139_ = lean_array_get_borrowed(v___x_135_, v_es_134_, v_j_138_);
lean_dec(v_j_138_);
switch(lean_obj_tag(v___x_139_))
{
case 0:
{
lean_object* v_key_140_; uint8_t v___x_141_; 
v_key_140_ = lean_ctor_get(v___x_139_, 0);
v___x_141_ = lean_name_eq(v_x_133_, v_key_140_);
return v___x_141_;
}
case 1:
{
lean_object* v_node_142_; size_t v___x_143_; size_t v___x_144_; 
v_node_142_ = lean_ctor_get(v___x_139_, 0);
v___x_143_ = ((size_t)5ULL);
v___x_144_ = lean_usize_shift_right(v_x_132_, v___x_143_);
v_x_131_ = v_node_142_;
v_x_132_ = v___x_144_;
goto _start;
}
default: 
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
}
else
{
lean_object* v_ks_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_ks_147_ = lean_ctor_get(v_x_131_, 0);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_ks_147_, v___x_148_, v_x_133_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
size_t v_x_506__boxed_153_; uint8_t v_res_154_; lean_object* v_r_155_; 
v_x_506__boxed_153_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_res_154_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_150_, v_x_506__boxed_153_, v_x_152_);
lean_dec(v_x_152_);
lean_dec_ref(v_x_150_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_156_; uint64_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1723u);
v___x_157_ = lean_uint64_of_nat(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
uint64_t v___y_161_; 
if (lean_obj_tag(v_x_159_) == 0)
{
uint64_t v___x_164_; 
v___x_164_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0);
v___y_161_ = v___x_164_;
goto v___jp_160_;
}
else
{
uint64_t v_hash_165_; 
v_hash_165_ = lean_ctor_get_uint64(v_x_159_, sizeof(void*)*2);
v___y_161_ = v_hash_165_;
goto v___jp_160_;
}
v___jp_160_:
{
size_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_uint64_to_usize(v___y_161_);
v___x_163_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_158_, v___x_162_, v_x_159_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___boxed(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_x_166_, v_x_167_);
lean_dec(v_x_167_);
lean_dec_ref(v_x_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(lean_object* v_xs_170_, lean_object* v_v_171_, lean_object* v_i_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_array_get_size(v_xs_170_);
v___x_174_ = lean_nat_dec_lt(v_i_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_i_172_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_array_fget_borrowed(v_xs_170_, v_i_172_);
v___x_177_ = lean_name_eq(v___x_176_, v_v_171_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_i_172_, v___x_178_);
lean_dec(v_i_172_);
v_i_172_ = v___x_179_;
goto _start;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_i_172_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_xs_182_, lean_object* v_v_183_, lean_object* v_i_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(v_xs_182_, v_v_183_, v_i_184_);
lean_dec(v_v_183_);
lean_dec_ref(v_xs_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(lean_object* v_xs_186_, lean_object* v_v_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(v_xs_186_, v_v_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4___boxed(lean_object* v_xs_190_, lean_object* v_v_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(v_xs_190_, v_v_191_);
lean_dec(v_v_191_);
lean_dec_ref(v_xs_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(lean_object* v_x_193_, size_t v_x_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v_es_196_; lean_object* v___x_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v_j_200_; lean_object* v_entry_201_; 
v_es_196_ = lean_ctor_get(v_x_193_, 0);
v___x_197_ = lean_box(2);
v___x_198_ = ((size_t)31ULL);
v___x_199_ = lean_usize_land(v_x_194_, v___x_198_);
v_j_200_ = lean_usize_to_nat(v___x_199_);
v_entry_201_ = lean_array_get(v___x_197_, v_es_196_, v_j_200_);
switch(lean_obj_tag(v_entry_201_))
{
case 0:
{
lean_object* v_key_202_; uint8_t v___x_203_; 
v_key_202_ = lean_ctor_get(v_entry_201_, 0);
lean_inc(v_key_202_);
lean_dec_ref_known(v_entry_201_, 2);
v___x_203_ = lean_name_eq(v_x_195_, v_key_202_);
lean_dec(v_key_202_);
if (v___x_203_ == 0)
{
lean_dec(v_j_200_);
return v_x_193_;
}
else
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
lean_inc_ref(v_es_196_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_x_193_, 0);
lean_dec(v_unused_212_);
v___x_205_ = v_x_193_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_dec(v_x_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_array_set(v_es_196_, v_j_200_, v___x_197_);
lean_dec(v_j_200_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
case 1:
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_247_; 
lean_inc_ref(v_es_196_);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v_x_193_, 0);
lean_dec(v_unused_248_);
v___x_214_ = v_x_193_;
v_isShared_215_ = v_isSharedCheck_247_;
goto v_resetjp_213_;
}
else
{
lean_dec(v_x_193_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_247_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_node_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_246_; 
v_node_216_ = lean_ctor_get(v_entry_201_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_entry_201_);
if (v_isSharedCheck_246_ == 0)
{
v___x_218_ = v_entry_201_;
v_isShared_219_ = v_isSharedCheck_246_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_node_216_);
lean_dec(v_entry_201_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_246_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
size_t v___x_220_; lean_object* v_entries_221_; size_t v___x_222_; lean_object* v_newNode_223_; lean_object* v___x_224_; 
v___x_220_ = ((size_t)5ULL);
v_entries_221_ = lean_array_set(v_es_196_, v_j_200_, v___x_197_);
v___x_222_ = lean_usize_shift_right(v_x_194_, v___x_220_);
v_newNode_223_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_node_216_, v___x_222_, v_x_195_);
lean_inc_ref(v_newNode_223_);
v___x_224_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_226_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v_newNode_223_);
v___x_226_ = v___x_218_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_newNode_223_);
v___x_226_ = v_reuseFailAlloc_231_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_array_set(v_entries_221_, v_j_200_, v___x_226_);
lean_dec(v_j_200_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_227_);
v___x_229_ = v___x_214_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v_val_232_; lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v_newNode_223_);
lean_del_object(v___x_218_);
v_val_232_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v___x_224_, 1);
v_fst_233_ = lean_ctor_get(v_val_232_, 0);
v_snd_234_ = lean_ctor_get(v_val_232_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_val_232_);
if (v_isSharedCheck_245_ == 0)
{
v___x_236_ = v_val_232_;
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_snd_234_);
lean_inc(v_fst_233_);
lean_dec(v_val_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_snd_234_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_array_set(v_entries_221_, v_j_200_, v___x_239_);
lean_dec(v_j_200_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_240_);
v___x_242_ = v___x_214_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_200_);
return v_x_193_;
}
}
}
else
{
lean_object* v_ks_249_; lean_object* v_vs_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_264_; 
v_ks_249_ = lean_ctor_get(v_x_193_, 0);
v_vs_250_ = lean_ctor_get(v_x_193_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_264_ == 0)
{
v___x_252_ = v_x_193_;
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_vs_250_);
lean_inc(v_ks_249_);
lean_dec(v_x_193_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_264_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; 
v___x_254_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(v_ks_249_, v_x_195_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_256_; 
if (v_isShared_253_ == 0)
{
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_ks_249_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_vs_250_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
else
{
lean_object* v_val_258_; lean_object* v_keys_x27_259_; lean_object* v_vals_x27_260_; lean_object* v___x_262_; 
v_val_258_ = lean_ctor_get(v___x_254_, 0);
lean_inc_n(v_val_258_, 2);
lean_dec_ref_known(v___x_254_, 1);
v_keys_x27_259_ = l_Array_eraseIdx___redArg(v_ks_249_, v_val_258_);
v_vals_x27_260_ = l_Array_eraseIdx___redArg(v_vs_250_, v_val_258_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_vals_x27_260_);
lean_ctor_set(v___x_252_, 0, v_keys_x27_259_);
v___x_262_ = v___x_252_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_keys_x27_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_vals_x27_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg___boxed(lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
size_t v_x_591__boxed_268_; lean_object* v_res_269_; 
v_x_591__boxed_268_ = lean_unbox_usize(v_x_266_);
lean_dec(v_x_266_);
v_res_269_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_265_, v_x_591__boxed_268_, v_x_267_);
lean_dec(v_x_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
uint64_t v___y_273_; 
if (lean_obj_tag(v_x_271_) == 0)
{
uint64_t v___x_276_; 
v___x_276_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0);
v___y_273_ = v___x_276_;
goto v___jp_272_;
}
else
{
uint64_t v_hash_277_; 
v_hash_277_ = lean_ctor_get_uint64(v_x_271_, sizeof(void*)*2);
v___y_273_ = v_hash_277_;
goto v___jp_272_;
}
v___jp_272_:
{
size_t v_h_274_; lean_object* v___x_275_; 
v_h_274_ = lean_uint64_to_usize(v___y_273_);
v___x_275_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_270_, v_h_274_, v_x_271_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_x_278_, v_x_279_);
lean_dec(v_x_279_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object* v_s_287_, lean_object* v_declName_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_s_287_, v_declName_288_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_s_287_);
v___x_293_ = lean_obj_once(&l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1, &l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1_once, _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1);
v___x_294_ = l_Lean_MessageData_ofConstName(v_declName_288_, v___x_292_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_obj_once(&l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3, &l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3_once, _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v___x_297_, v_a_289_, v_a_290_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_s_287_, v_declName_288_);
lean_dec(v_declName_288_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl___boxed(lean_object* v_s_301_, lean_object* v_declName_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_s_301_, v_declName_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
return v_res_306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(lean_object* v_00_u03b2_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_x_308_, v_x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___boxed(lean_object* v_00_u03b2_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(v_00_u03b2_311_, v_x_312_, v_x_313_);
lean_dec(v_x_313_);
lean_dec_ref(v_x_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(lean_object* v_00_u03b2_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_x_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___boxed(lean_object* v_00_u03b2_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(v_00_u03b2_320_, v_x_321_, v_x_322_);
lean_dec(v_x_322_);
return v_res_323_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(lean_object* v_00_u03b2_324_, lean_object* v_x_325_, size_t v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_325_, v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
size_t v_x_799__boxed_333_; uint8_t v_res_334_; lean_object* v_r_335_; 
v_x_799__boxed_333_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_res_334_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(v_00_u03b2_329_, v_x_330_, v_x_799__boxed_333_, v_x_332_);
lean_dec(v_x_332_);
lean_dec_ref(v_x_330_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, size_t v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_337_, v_x_338_, v_x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
size_t v_x_810__boxed_345_; lean_object* v_res_346_; 
v_x_810__boxed_345_ = lean_unbox_usize(v_x_343_);
lean_dec(v_x_343_);
v_res_346_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(v_00_u03b2_341_, v_x_342_, v_x_810__boxed_345_, v_x_344_);
lean_dec(v_x_344_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_347_, lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_heq_350_, lean_object* v_i_351_, lean_object* v_k_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_keys_348_, v_i_351_, v_k_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_354_, lean_object* v_keys_355_, lean_object* v_vals_356_, lean_object* v_heq_357_, lean_object* v_i_358_, lean_object* v_k_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(v_00_u03b2_354_, v_keys_355_, v_vals_356_, v_heq_357_, v_i_358_, v_k_359_);
lean_dec(v_k_359_);
lean_dec_ref(v_vals_356_);
lean_dec_ref(v_keys_355_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
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
