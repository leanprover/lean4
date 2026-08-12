// Lean compiler output
// Module: Lean.OrderLevel
// Imports: public import Lean.CoreM import Lean.Expr
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__0 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__0_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "` is expected to take exactly one universe parameter"};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__2 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__2_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__3;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "the first argument of `"};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__4 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__4_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__5;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is expected to be its carrier"};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__6 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__6_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__7;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "the carrier of `"};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__8 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__8_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__9;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` is `Sort "};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__10 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__10_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__11;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "`, which is neither `Sort "};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__12 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__12_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__13;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` nor `Type "};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__14 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__14_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__15;
static const lean_string_object l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown constant `"};
static const lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__16 = (const lean_object*)&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__16_value;
static lean_once_cell_t l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_initFn_00___x40_Lean_OrderLevel_2903456480____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_initFn_00___x40_Lean_OrderLevel_2903456480____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_leCarrierIsSortCache;
static const lean_string_object l_Lean_leCarrierIsSort___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_leCarrierIsSort___closed__0 = (const lean_object*)&l_Lean_leCarrierIsSort___closed__0_value;
static const lean_ctor_object l_Lean_leCarrierIsSort___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_leCarrierIsSort___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l_Lean_leCarrierIsSort___closed__1 = (const lean_object*)&l_Lean_leCarrierIsSort___closed__1_value;
static const lean_string_object l_Lean_leCarrierIsSort___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_leCarrierIsSort___closed__2 = (const lean_object*)&l_Lean_leCarrierIsSort___closed__2_value;
static const lean_ctor_object l_Lean_leCarrierIsSort___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_leCarrierIsSort___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l_Lean_leCarrierIsSort___closed__3 = (const lean_object*)&l_Lean_leCarrierIsSort___closed__3_value;
static const lean_string_object l_Lean_leCarrierIsSort___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`LE` and `LT` disagree on whether their carrier is a `Sort` or a `Type`"};
static const lean_object* l_Lean_leCarrierIsSort___closed__4 = (const lean_object*)&l_Lean_leCarrierIsSort___closed__4_value;
static lean_once_cell_t l_Lean_leCarrierIsSort___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_leCarrierIsSort___closed__5;
LEAN_EXPORT lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_leCarrierIsSort___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v_options_26_ = lean_ctor_get(v___y_21_, 2);
v___x_27_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___closed__5);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0___boxed(lean_object* v_msgData_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0(v_msgData_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(lean_object* v_msg_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 5);
v___x_42_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0_spec__0(v_msg_37_, v___y_38_, v___y_39_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v_msg_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_56_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__0));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__2));
v___x_62_ = l_Lean_stringToMessageData(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__4));
v___x_65_ = l_Lean_stringToMessageData(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__7(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__6));
v___x_68_ = l_Lean_stringToMessageData(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__9(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__8));
v___x_71_ = l_Lean_stringToMessageData(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__11(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__10));
v___x_74_ = l_Lean_stringToMessageData(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__13(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__12));
v___x_77_ = l_Lean_stringToMessageData(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__15(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__14));
v___x_80_ = l_Lean_stringToMessageData(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__17(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__16));
v___x_83_ = l_Lean_stringToMessageData(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached(lean_object* v_declName_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___x_106_; lean_object* v_env_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v___x_106_ = lean_st_ref_get(v_a_86_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = 0;
lean_inc(v_declName_84_);
v___x_109_ = l_Lean_Environment_find_x3f(v_env_107_, v_declName_84_, v___x_108_);
if (lean_obj_tag(v___x_109_) == 1)
{
lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_156_; 
v_val_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_156_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_156_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_156_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_ConstantInfo_levelParams(v_val_110_);
if (lean_obj_tag(v___x_114_) == 1)
{
lean_object* v_tail_115_; 
v_tail_115_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_tail_115_);
if (lean_obj_tag(v_tail_115_) == 0)
{
lean_object* v_head_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_154_; 
v_head_116_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v___x_114_, 1);
lean_dec(v_unused_155_);
v___x_118_ = v___x_114_;
v_isShared_119_ = v_isSharedCheck_154_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_head_116_);
lean_dec(v___x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_154_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_ConstantInfo_type(v_val_110_);
lean_dec(v_val_110_);
if (lean_obj_tag(v___x_120_) == 7)
{
lean_object* v_binderType_121_; 
v_binderType_121_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_binderType_121_);
lean_dec_ref_known(v___x_120_, 3);
if (lean_obj_tag(v_binderType_121_) == 3)
{
lean_object* v_u_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_u_122_ = lean_ctor_get(v_binderType_121_, 0);
lean_inc(v_u_122_);
lean_dec_ref_known(v_binderType_121_, 1);
lean_inc(v_head_116_);
v___x_123_ = l_Lean_Level_param___override(v_head_116_);
v___x_124_ = lean_level_eq(v_u_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = l_Lean_Level_succ___override(v___x_123_);
v___x_126_ = lean_level_eq(v_u_122_, v___x_125_);
lean_dec(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
lean_del_object(v___x_112_);
v___x_127_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__9, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__9_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__9);
v___x_128_ = l_Lean_MessageData_ofName(v_declName_84_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 7);
lean_ctor_set(v___x_118_, 1, v___x_128_);
lean_ctor_set(v___x_118_, 0, v___x_127_);
v___x_130_ = v___x_118_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_145_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_131_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__11, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__11_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__11);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = l_Lean_MessageData_ofLevel(v_u_122_);
v___x_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__13, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__13_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__13);
v___x_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = l_Lean_MessageData_ofName(v_head_116_);
lean_inc_ref(v___x_137_);
v___x_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__15, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__15_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__15);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_137_);
v___x_142_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1);
v___x_143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v___x_143_, v_a_85_, v_a_86_);
return v___x_144_;
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_148_; 
lean_dec(v_u_122_);
lean_del_object(v___x_118_);
lean_dec(v_head_116_);
lean_dec(v_declName_84_);
v___x_146_ = lean_box(v___x_124_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_146_);
v___x_148_ = v___x_112_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_dec(v___x_123_);
lean_dec(v_u_122_);
lean_del_object(v___x_118_);
lean_dec(v_head_116_);
lean_dec(v_declName_84_);
v___x_150_ = lean_box(v___x_124_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_150_);
v___x_152_ = v___x_112_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_dec_ref(v_binderType_121_);
lean_del_object(v___x_118_);
lean_dec(v_head_116_);
lean_del_object(v___x_112_);
v___y_98_ = v_a_85_;
v___y_99_ = v_a_86_;
goto v___jp_97_;
}
}
else
{
lean_dec_ref(v___x_120_);
lean_del_object(v___x_118_);
lean_dec(v_head_116_);
lean_del_object(v___x_112_);
v___y_98_ = v_a_85_;
v___y_99_ = v_a_86_;
goto v___jp_97_;
}
}
}
else
{
lean_dec_ref_known(v___x_114_, 2);
lean_dec(v_tail_115_);
lean_del_object(v___x_112_);
lean_dec(v_val_110_);
v___y_89_ = v_a_85_;
v___y_90_ = v_a_86_;
goto v___jp_88_;
}
}
else
{
lean_dec(v___x_114_);
lean_del_object(v___x_112_);
lean_dec(v_val_110_);
v___y_89_ = v_a_85_;
v___y_90_ = v_a_86_;
goto v___jp_88_;
}
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_109_);
v___x_157_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__17, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__17_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__17);
v___x_158_ = l_Lean_MessageData_ofName(v_declName_84_);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v___x_161_, v_a_85_, v_a_86_);
return v___x_162_;
}
v___jp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_91_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__1);
v___x_92_ = l_Lean_MessageData_ofName(v_declName_84_);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__3, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__3_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__3);
v___x_95_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v___x_95_, v___y_89_, v___y_90_);
return v___x_96_;
}
v___jp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_100_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__5, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__5_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__5);
v___x_101_ = l_Lean_MessageData_ofName(v_declName_84_);
v___x_102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_obj_once(&l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__7, &l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__7_once, _init_l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___closed__7);
v___x_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v___x_104_, v___y_98_, v___y_99_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached___boxed(lean_object* v_declName_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached(v_declName_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0(lean_object* v_00_u03b1_168_, lean_object* v_msg_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v_msg_169_, v___y_170_, v___y_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___boxed(lean_object* v_00_u03b1_174_, lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0(v_00_u03b1_174_, v_msg_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_initFn_00___x40_Lean_OrderLevel_2903456480____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_box(0);
v___x_182_ = lean_st_mk_ref(v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_OrderLevel_0__Lean_initFn_00___x40_Lean_OrderLevel_2903456480____hygCtx___hyg_2____boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_OrderLevel_0__Lean_initFn_00___x40_Lean_OrderLevel_2903456480____hygCtx___hyg_2_();
return v_res_185_;
}
}
static lean_object* _init_l_Lean_leCarrierIsSort___closed__5(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_leCarrierIsSort___closed__4));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_leCarrierIsSort(lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = l_Lean_leCarrierIsSortCache;
v___x_199_ = lean_st_ref_get(v___x_198_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_val_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 0);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_val_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v___x_199_);
v___x_208_ = ((lean_object*)(l_Lean_leCarrierIsSort___closed__1));
v___x_209_ = l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached(v___x_208_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_237_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_237_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_237_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_237_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Lean_leCarrierIsSort___closed__3));
v___x_221_ = l___private_Lean_OrderLevel_0__Lean_carrierIsSortUncached(v___x_220_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; uint8_t v___x_234_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 1);
v___x_234_ = lean_unbox(v_a_210_);
if (v___x_234_ == 0)
{
uint8_t v___x_235_; 
v___x_235_ = lean_unbox(v_a_222_);
lean_dec(v_a_222_);
if (v___x_235_ == 0)
{
goto v___jp_214_;
}
else
{
lean_del_object(v___x_212_);
lean_dec(v_a_210_);
goto v___jp_223_;
}
}
else
{
uint8_t v___x_236_; 
v___x_236_ = lean_unbox(v_a_222_);
lean_dec(v_a_222_);
if (v___x_236_ == 0)
{
lean_del_object(v___x_212_);
lean_dec(v_a_210_);
goto v___jp_223_;
}
else
{
goto v___jp_214_;
}
}
v___jp_223_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v___x_224_ = lean_obj_once(&l_Lean_leCarrierIsSort___closed__5, &l_Lean_leCarrierIsSort___closed__5_once, _init_l_Lean_leCarrierIsSort___closed__5);
v___x_225_ = l_Lean_throwError___at___00__private_Lean_OrderLevel_0__Lean_carrierIsSortUncached_spec__0___redArg(v___x_224_, v_a_195_, v_a_196_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_del_object(v___x_212_);
lean_dec(v_a_210_);
return v___x_221_;
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_inc(v_a_210_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_a_210_);
v___x_216_ = lean_st_ref_set(v___x_198_, v___x_215_);
if (v_isShared_213_ == 0)
{
v___x_218_ = v___x_212_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_210_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_leCarrierIsSort___boxed(lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_leCarrierIsSort(v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
return v_res_241_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_OrderLevel_0__Lean_initFn_00___x40_Lean_OrderLevel_2903456480____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_leCarrierIsSortCache = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_leCarrierIsSortCache);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_OrderLevel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_OrderLevel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_OrderLevel(builtin);
}
#ifdef __cplusplus
}
#endif
