// Lean compiler output
// Module: Lean.ExtraModUses
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr import Init.Data.Range.Polymorphic.Stream
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqIndirectModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqIndirectModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqIndirectModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqIndirectModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqIndirectModUse___closed__0 = (const lean_object*)&l_Lean_instBEqIndirectModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqIndirectModUse = (const lean_object*)&l_Lean_instBEqIndirectModUse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static const lean_ctor_object l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "indirectModUseExt"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 173, 36, 115, 222, 236, 117, 108)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_indirectModUseExt;
static const lean_closure_object l_Lean_getIndirectModUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getIndirectModUses___closed__0 = (const lean_object*)&l_Lean_getIndirectModUses___closed__0_value;
static const lean_closure_object l_Lean_getIndirectModUses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getIndirectModUses___closed__1 = (const lean_object*)&l_Lean_getIndirectModUses___closed__1_value;
static lean_once_cell_t l_Lean_getIndirectModUses___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIndirectModUses___closed__2;
static lean_once_cell_t l_Lean_getIndirectModUses___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIndirectModUses___closed__3;
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "recording indirect mod use of `"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__1;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "` ("};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__3;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqExtraModUse___closed__0 = (const lean_object*)&l_Lean_instBEqExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqExtraModUse = (const lean_object*)&l_Lean_instBEqExtraModUse___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableExtraModUse___closed__0 = (const lean_object*)&l_Lean_instHashableExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableExtraModUse = (const lean_object*)&l_Lean_instHashableExtraModUse___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isExported"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__15 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprExtraModUse_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprExtraModUse___closed__0 = (const lean_object*)&l_Lean_instReprExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprExtraModUse = (const lean_object*)&l_Lean_instReprExtraModUse___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1(lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object*);
static lean_once_cell_t l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 226, 202, 112, 104, 166, 144, 212)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
static lean_once_cell_t l_Lean_getExtraModUses___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__0;
static lean_once_cell_t l_Lean_getExtraModUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__1;
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isExtraRevModUseExt"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 0, 44, 18, 118, 38, 4, 21)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
static const lean_ctor_object l_Lean_isExtraRevModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isExtraRevModUse___closed__0 = (const lean_object*)&l_Lean_isExtraRevModUse___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "recording extra reverse use of current module"};
static const lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ExtraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 69, 125, 143, 117, 200, 37, 103)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(163, 125, 98, 145, 27, 242, 139, 173)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 80, 45, 80, 85, 236, 79, 117)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 211, 254, 26, 237, 216, 211, 30)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 203, 147, 114, 124, 159, 234, 194)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 198, 100, 78, 72, 145, 180, 196)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 126, 81, 65, 191, 6, 222, 76)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqIndirectModUse_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_kind_3_; lean_object* v_declName_4_; lean_object* v_kind_5_; lean_object* v_declName_6_; uint8_t v___x_7_; 
v_kind_3_ = lean_ctor_get(v_x_1_, 0);
v_declName_4_ = lean_ctor_get(v_x_1_, 1);
v_kind_5_ = lean_ctor_get(v_x_2_, 0);
v_declName_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_string_dec_eq(v_kind_3_, v_kind_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_name_eq(v_declName_4_, v_declName_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqIndirectModUse_beq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_instBEqIndirectModUse_beq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_array_mk(v_es_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_s_17_, lean_object* v_x_18_){
_start:
{
lean_inc_ref(v_s_17_);
return v_s_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_s_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_s_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_s_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object* v_val_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___y_27_; 
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_27_ = v___x_30_;
goto v___jp_26_;
}
else
{
lean_object* v_val_31_; 
v_val_31_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_val_31_);
lean_dec_ref(v_x_25_);
v___y_27_ = v_val_31_;
goto v___jp_26_;
}
v___jp_26_:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_array_push(v___y_27_, v_val_24_);
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_val_32_, lean_object* v_a_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v_val_37_; lean_object* v___x_38_; 
v___x_35_ = lean_box(0);
v___x_36_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_32_, v___x_35_);
v_val_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_val_37_);
lean_dec(v___x_36_);
v___x_38_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_38_, 0, v_a_33_);
lean_ctor_set(v___x_38_, 1, v_val_37_);
lean_ctor_set(v___x_38_, 2, v_x_34_);
return v___x_38_;
}
else
{
lean_object* v_key_39_; lean_object* v_value_40_; lean_object* v_tail_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_56_; 
v_key_39_ = lean_ctor_get(v_x_34_, 0);
v_value_40_ = lean_ctor_get(v_x_34_, 1);
v_tail_41_ = lean_ctor_get(v_x_34_, 2);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_56_ == 0)
{
v___x_43_ = v_x_34_;
v_isShared_44_ = v_isSharedCheck_56_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_tail_41_);
lean_inc(v_value_40_);
lean_inc(v_key_39_);
lean_dec(v_x_34_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_56_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
uint8_t v___x_45_; 
v___x_45_ = lean_name_eq(v_key_39_, v_a_33_);
if (v___x_45_ == 0)
{
lean_object* v_tail_46_; lean_object* v___x_48_; 
v_tail_46_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_32_, v_a_33_, v_tail_41_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 2, v_tail_46_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_key_39_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_value_40_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v_tail_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_val_52_; lean_object* v___x_54_; 
lean_dec(v_key_39_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v_value_40_);
v___x_51_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_32_, v___x_50_);
v_val_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_val_52_);
lean_dec(v___x_51_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v_val_52_);
lean_ctor_set(v___x_43_, 0, v_a_33_);
v___x_54_ = v___x_43_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_33_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_val_52_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v_tail_41_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
else
{
lean_object* v_key_60_; lean_object* v_tail_61_; uint8_t v___x_62_; 
v_key_60_ = lean_ctor_get(v_x_58_, 0);
v_tail_61_ = lean_ctor_get(v_x_58_, 2);
v___x_62_ = lean_name_eq(v_key_60_, v_a_57_);
if (v___x_62_ == 0)
{
v_x_58_ = v_tail_61_;
goto _start;
}
else
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_a_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_68_; uint64_t v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(1723u);
v___x_69_ = lean_uint64_of_nat(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
return v_x_70_;
}
else
{
lean_object* v_key_72_; lean_object* v_value_73_; lean_object* v_tail_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_100_; 
v_key_72_ = lean_ctor_get(v_x_71_, 0);
v_value_73_ = lean_ctor_get(v_x_71_, 1);
v_tail_74_ = lean_ctor_get(v_x_71_, 2);
v_isSharedCheck_100_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_100_ == 0)
{
v___x_76_ = v_x_71_;
v_isShared_77_ = v_isSharedCheck_100_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_tail_74_);
lean_inc(v_value_73_);
lean_inc(v_key_72_);
lean_dec(v_x_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_100_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; uint64_t v___y_80_; 
v___x_78_ = lean_array_get_size(v_x_70_);
if (lean_obj_tag(v_key_72_) == 0)
{
uint64_t v___x_98_; 
v___x_98_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_80_ = v___x_98_;
goto v___jp_79_;
}
else
{
uint64_t v_hash_99_; 
v_hash_99_ = lean_ctor_get_uint64(v_key_72_, sizeof(void*)*2);
v___y_80_ = v_hash_99_;
goto v___jp_79_;
}
v___jp_79_:
{
uint64_t v___x_81_; uint64_t v___x_82_; uint64_t v_fold_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_81_ = 32ULL;
v___x_82_ = lean_uint64_shift_right(v___y_80_, v___x_81_);
v_fold_83_ = lean_uint64_xor(v___y_80_, v___x_82_);
v___x_84_ = 16ULL;
v___x_85_ = lean_uint64_shift_right(v_fold_83_, v___x_84_);
v___x_86_ = lean_uint64_xor(v_fold_83_, v___x_85_);
v___x_87_ = lean_uint64_to_usize(v___x_86_);
v___x_88_ = lean_usize_of_nat(v___x_78_);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_sub(v___x_88_, v___x_89_);
v___x_91_ = lean_usize_land(v___x_87_, v___x_90_);
v___x_92_ = lean_array_uget_borrowed(v_x_70_, v___x_91_);
lean_inc(v___x_92_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 2, v___x_92_);
v___x_94_ = v___x_76_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_key_72_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_value_73_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_97_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = lean_array_uset(v_x_70_, v___x_91_, v___x_94_);
v_x_70_ = v___x_95_;
v_x_71_ = v_tail_74_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_101_, lean_object* v_source_102_, lean_object* v_target_103_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_array_get_size(v_source_102_);
v___x_105_ = lean_nat_dec_lt(v_i_101_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec_ref(v_source_102_);
lean_dec(v_i_101_);
return v_target_103_;
}
else
{
lean_object* v_es_106_; lean_object* v___x_107_; lean_object* v_source_108_; lean_object* v_target_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_es_106_ = lean_array_fget(v_source_102_, v_i_101_);
v___x_107_ = lean_box(0);
v_source_108_ = lean_array_fset(v_source_102_, v_i_101_, v___x_107_);
v_target_109_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_target_103_, v_es_106_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_i_101_, v___x_110_);
lean_dec(v_i_101_);
v_i_101_ = v___x_111_;
v_source_102_ = v_source_108_;
v_target_103_ = v_target_109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_nbuckets_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_114_ = lean_array_get_size(v_data_113_);
v___x_115_ = lean_unsigned_to_nat(2u);
v_nbuckets_116_ = lean_nat_mul(v___x_114_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_box(0);
v___x_119_ = lean_mk_array(v_nbuckets_116_, v___x_118_);
v___x_120_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_117_, v_data_113_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_val_121_, lean_object* v_m_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___y_125_; lean_object* v___y_126_; size_t v___y_127_; lean_object* v___y_128_; lean_object* v_size_131_; lean_object* v_buckets_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_179_; 
v_size_131_ = lean_ctor_get(v_m_122_, 0);
v_buckets_132_ = lean_ctor_get(v_m_122_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_m_122_);
if (v_isSharedCheck_179_ == 0)
{
v___x_134_ = v_m_122_;
v_isShared_135_ = v_isSharedCheck_179_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_buckets_132_);
lean_inc(v_size_131_);
lean_dec(v_m_122_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_179_;
goto v_resetjp_133_;
}
v___jp_124_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_array_uset(v___y_126_, v___y_127_, v___y_125_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___y_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; uint64_t v___y_138_; 
v___x_136_ = lean_array_get_size(v_buckets_132_);
if (lean_obj_tag(v_a_123_) == 0)
{
uint64_t v___x_177_; 
v___x_177_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_138_ = v___x_177_;
goto v___jp_137_;
}
else
{
uint64_t v_hash_178_; 
v_hash_178_ = lean_ctor_get_uint64(v_a_123_, sizeof(void*)*2);
v___y_138_ = v_hash_178_;
goto v___jp_137_;
}
v___jp_137_:
{
uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___y_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___y_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_136_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_132_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_123_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_size_x27_155_; lean_object* v___x_156_; lean_object* v_buckets_x27_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_152_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___x_153_ = lean_array_push(v___x_152_, v_val_121_);
v___x_154_ = lean_unsigned_to_nat(1u);
v_size_x27_155_ = lean_nat_add(v_size_131_, v___x_154_);
lean_dec(v_size_131_);
lean_inc(v_bkt_150_);
v___x_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_156_, 0, v_a_123_);
lean_ctor_set(v___x_156_, 1, v___x_153_);
lean_ctor_set(v___x_156_, 2, v_bkt_150_);
v_buckets_x27_157_ = lean_array_uset(v_buckets_132_, v___x_149_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(4u);
v___x_159_ = lean_nat_mul(v_size_x27_155_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(3u);
v___x_161_ = lean_nat_div(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_array_get_size(v_buckets_x27_157_);
v___x_163_ = lean_nat_dec_le(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v_val_164_; lean_object* v___x_166_; 
v_val_164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_157_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_val_164_);
lean_ctor_set(v___x_134_, 0, v_size_x27_155_);
v___x_166_ = v___x_134_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_size_x27_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_val_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_object* v___x_169_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_buckets_x27_157_);
lean_ctor_set(v___x_134_, 0, v_size_x27_155_);
v___x_169_ = v___x_134_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_x27_155_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_buckets_x27_157_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v___x_171_; lean_object* v_buckets_x27_172_; lean_object* v_bkt_x27_173_; uint8_t v___x_174_; 
lean_inc(v_bkt_150_);
lean_del_object(v___x_134_);
v___x_171_ = lean_box(0);
v_buckets_x27_172_ = lean_array_uset(v_buckets_132_, v___x_149_, v___x_171_);
lean_inc(v_a_123_);
v_bkt_x27_173_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_121_, v_a_123_, v_bkt_150_);
v___x_174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_123_, v_bkt_x27_173_);
lean_dec(v_a_123_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_sub(v_size_131_, v___x_175_);
lean_dec(v_size_131_);
v___y_125_ = v_bkt_x27_173_;
v___y_126_ = v_buckets_x27_172_;
v___y_127_ = v___x_149_;
v___y_128_ = v___x_176_;
goto v___jp_124_;
}
else
{
v___y_125_ = v_bkt_x27_173_;
v___y_126_ = v_buckets_x27_172_;
v___y_127_ = v___x_149_;
v___y_128_ = v_size_131_;
goto v___jp_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_val_180_, lean_object* v_as_181_, size_t v_sz_182_, size_t v_i_183_, lean_object* v_b_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = lean_usize_dec_lt(v_i_183_, v_sz_182_);
if (v___x_185_ == 0)
{
lean_dec(v_val_180_);
return v_b_184_;
}
else
{
lean_object* v_a_186_; lean_object* v_declName_187_; lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; 
v_a_186_ = lean_array_uget_borrowed(v_as_181_, v_i_183_);
v_declName_187_ = lean_ctor_get(v_a_186_, 1);
lean_inc(v_declName_187_);
lean_inc(v_val_180_);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_180_, v_b_184_, v_declName_187_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_183_, v___x_189_);
v_i_183_ = v___x_190_;
v_b_184_ = v___x_188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_val_192_, lean_object* v_as_193_, lean_object* v_sz_194_, lean_object* v_i_195_, lean_object* v_b_196_){
_start:
{
size_t v_sz_boxed_197_; size_t v_i_boxed_198_; lean_object* v_res_199_; 
v_sz_boxed_197_ = lean_unbox_usize(v_sz_194_);
lean_dec(v_sz_194_);
v_i_boxed_198_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_192_, v_as_193_, v_sz_boxed_197_, v_i_boxed_198_, v_b_196_);
lean_dec_ref(v_as_193_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_as_200_, size_t v_sz_201_, size_t v_i_202_, lean_object* v_b_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_204_ == 0)
{
return v_b_203_;
}
else
{
lean_object* v_snd_205_; 
v_snd_205_ = lean_ctor_get(v_b_203_, 1);
lean_inc(v_snd_205_);
if (lean_obj_tag(v_snd_205_) == 0)
{
lean_object* v_fst_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_fst_206_ = lean_ctor_get(v_b_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_b_203_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_b_203_, 1);
lean_dec(v_unused_214_);
v___x_208_ = v_b_203_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_fst_206_);
lean_dec(v_b_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_snd_205_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_object* v_fst_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_239_; 
v_fst_215_ = lean_ctor_get(v_b_203_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_b_203_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v_b_203_, 1);
lean_dec(v_unused_240_);
v___x_217_ = v_b_203_;
v_isShared_218_ = v_isSharedCheck_239_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_fst_215_);
lean_dec(v_b_203_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_239_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_238_; 
v_val_219_ = lean_ctor_get(v_snd_205_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_snd_205_);
if (v_isSharedCheck_238_ == 0)
{
v___x_221_ = v_snd_205_;
v_isShared_222_ = v_isSharedCheck_238_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v_snd_205_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_238_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_a_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_a_223_ = lean_array_uget_borrowed(v_as_200_, v_i_202_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_val_219_, v___x_224_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_225_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_237_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
size_t v_sz_228_; size_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v_sz_228_ = lean_array_size(v_a_223_);
v___x_229_ = ((size_t)0ULL);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_219_, v_a_223_, v_sz_228_, v___x_229_, v_fst_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_227_);
lean_ctor_set(v___x_217_, 0, v___x_230_);
v___x_232_ = v___x_217_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_227_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_202_, v___x_233_);
v_i_202_ = v___x_234_;
v_b_203_ = v___x_232_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_241_, lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_b_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_241_, v_sz_boxed_245_, v_i_boxed_246_, v_b_244_);
lean_dec_ref(v_as_241_);
return v_res_247_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_box(0);
v___x_249_ = lean_unsigned_to_nat(16u);
v___x_250_ = lean_mk_array(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_s_253_; 
v___x_251_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_252_ = lean_unsigned_to_nat(0u);
v_s_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_253_, 0, v___x_252_);
lean_ctor_set(v_s_253_, 1, v___x_251_);
return v_s_253_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_256_; lean_object* v_s_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_257_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_s_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_259_){
_start:
{
lean_object* v___x_260_; size_t v_sz_261_; size_t v___x_262_; lean_object* v___x_263_; lean_object* v_fst_264_; 
v___x_260_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_261_ = lean_array_size(v_es_259_);
v___x_262_ = ((size_t)0ULL);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_259_, v_sz_261_, v___x_262_, v___x_260_);
v_fst_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_fst_264_);
lean_dec_ref(v___x_263_);
return v_fst_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_265_);
lean_dec_ref(v_es_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_284_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_286_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_287_, lean_object* v_a_288_, lean_object* v_x_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_288_, v_x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_291_, lean_object* v_a_292_, lean_object* v_x_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_291_, v_a_292_, v_x_293_);
lean_dec(v_x_293_);
lean_dec(v_a_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_296_, lean_object* v_data_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_299_, lean_object* v_i_300_, lean_object* v_source_301_, lean_object* v_target_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_300_, v_source_301_, v_target_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_305_, v_x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__2(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_311_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_312_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__3(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object* v_env_316_, lean_object* v_modIdx_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; 
v___x_318_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__3, &l_Lean_getIndirectModUses___closed__3_once, _init_l_Lean_getIndirectModUses___closed__3);
v___x_319_ = l_Lean_indirectModUseExt;
v___x_320_ = 0;
v___x_321_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_318_, v___x_319_, v_env_316_, v_modIdx_317_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object* v_env_322_, lean_object* v_modIdx_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_getIndirectModUses(v_env_322_, v_modIdx_323_);
lean_dec(v_modIdx_323_);
lean_dec_ref(v_env_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object* v___x_325_, lean_object* v___x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_toEnvExtension_328_; lean_object* v_asyncMode_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_toEnvExtension_328_ = lean_ctor_get(v___x_325_, 0);
v_asyncMode_329_ = lean_ctor_get(v_toEnvExtension_328_, 2);
lean_inc(v_asyncMode_329_);
v___x_330_ = lean_box(0);
v___x_331_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_325_, v_x_327_, v___x_326_, v_asyncMode_329_, v___x_330_);
lean_dec(v_asyncMode_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object* v_modifyEnv_332_, lean_object* v___f_333_, lean_object* v_____r_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_apply_1(v_modifyEnv_332_, v___f_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__0));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__2));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__4));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object* v_modifyEnv_345_, lean_object* v___f_346_, lean_object* v_declName_347_, lean_object* v_kind_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_cls_353_, lean_object* v_toBind_354_, lean_object* v___f_355_, uint8_t v_____do__lift_356_){
_start:
{
if (v_____do__lift_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec(v___f_355_);
lean_dec(v_toBind_354_);
lean_dec(v_cls_353_);
lean_dec(v_inst_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_kind_348_);
lean_dec(v_declName_347_);
v___x_357_ = lean_apply_1(v_modifyEnv_345_, v___f_346_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec_ref(v___f_346_);
lean_dec(v_modifyEnv_345_);
v___x_358_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__1, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1);
v___x_359_ = l_Lean_MessageData_ofName(v_declName_347_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__3, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__3_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_stringToMessageData(v_kind_348_);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__5, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__5_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l_Lean_addTrace___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_inst_352_, v_cls_353_, v___x_366_);
v___x_368_ = lean_apply_4(v_toBind_354_, lean_box(0), lean_box(0), v___x_367_, v___f_355_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object* v_modifyEnv_369_, lean_object* v___f_370_, lean_object* v_declName_371_, lean_object* v_kind_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_cls_377_, lean_object* v_toBind_378_, lean_object* v___f_379_, lean_object* v_____do__lift_380_){
_start:
{
uint8_t v_____do__lift_466__boxed_381_; lean_object* v_res_382_; 
v_____do__lift_466__boxed_381_ = lean_unbox(v_____do__lift_380_);
v_res_382_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_modifyEnv_369_, v___f_370_, v_declName_371_, v_kind_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_cls_377_, v_toBind_378_, v___f_379_, v_____do__lift_466__boxed_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v___x_386_, lean_object* v_kind_387_, lean_object* v_declName_388_, lean_object* v___x_389_, lean_object* v_modifyEnv_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_toBind_395_, lean_object* v_inst_396_, lean_object* v_toApplicative_397_, lean_object* v_____do__lift_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_399_ = l_Lean_indirectModUseExt;
v___x_400_ = lean_box(2);
v___x_401_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_386_, v___x_399_, v_____do__lift_398_, v___x_400_);
lean_inc(v_declName_388_);
lean_inc_ref(v_kind_387_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_kind_387_);
lean_ctor_set(v___x_402_, 1, v_declName_388_);
lean_inc_ref(v___x_402_);
v___x_403_ = l_List_elem___redArg(v___x_389_, v___x_402_, v___x_401_);
if (v___x_403_ == 0)
{
lean_object* v___f_404_; lean_object* v___f_405_; lean_object* v_cls_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v_toApplicative_397_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_404_, 0, v___x_399_);
lean_closure_set(v___f_404_, 1, v___x_402_);
lean_inc_ref(v___f_404_);
lean_inc(v_modifyEnv_390_);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_405_, 0, v_modifyEnv_390_);
lean_closure_set(v___f_405_, 1, v___f_404_);
v_cls_406_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
lean_inc(v_toBind_395_);
lean_inc_ref(v_inst_392_);
lean_inc_ref(v_inst_391_);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_407_, 0, v_modifyEnv_390_);
lean_closure_set(v___f_407_, 1, v___f_404_);
lean_closure_set(v___f_407_, 2, v_declName_388_);
lean_closure_set(v___f_407_, 3, v_kind_387_);
lean_closure_set(v___f_407_, 4, v_inst_391_);
lean_closure_set(v___f_407_, 5, v_inst_392_);
lean_closure_set(v___f_407_, 6, v_inst_393_);
lean_closure_set(v___f_407_, 7, v_inst_394_);
lean_closure_set(v___f_407_, 8, v_cls_406_);
lean_closure_set(v___f_407_, 9, v_toBind_395_);
lean_closure_set(v___f_407_, 10, v___f_405_);
v___x_408_ = l_Lean_isTracingEnabledFor___redArg(v_inst_391_, v_inst_392_, v_inst_396_, v_cls_406_);
v___x_409_ = lean_apply_4(v_toBind_395_, lean_box(0), lean_box(0), v___x_408_, v___f_407_);
return v___x_409_;
}
else
{
lean_object* v_toPure_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___x_402_);
lean_dec(v_inst_396_);
lean_dec(v_toBind_395_);
lean_dec(v_inst_394_);
lean_dec_ref(v_inst_393_);
lean_dec_ref(v_inst_392_);
lean_dec_ref(v_inst_391_);
lean_dec(v_modifyEnv_390_);
lean_dec(v_declName_388_);
lean_dec_ref(v_kind_387_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_397_, 1);
lean_inc(v_toPure_410_);
lean_dec_ref(v_toApplicative_397_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_apply_2(v_toPure_410_, lean_box(0), v___x_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_kind_419_, lean_object* v_declName_420_){
_start:
{
lean_object* v_toApplicative_421_; lean_object* v_toBind_422_; lean_object* v_getEnv_423_; lean_object* v_modifyEnv_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___x_428_; 
v_toApplicative_421_ = lean_ctor_get(v_inst_413_, 0);
lean_inc_ref(v_toApplicative_421_);
v_toBind_422_ = lean_ctor_get(v_inst_413_, 1);
lean_inc(v_toBind_422_);
v_getEnv_423_ = lean_ctor_get(v_inst_414_, 0);
lean_inc(v_getEnv_423_);
v_modifyEnv_424_ = lean_ctor_get(v_inst_414_, 1);
lean_inc(v_modifyEnv_424_);
lean_dec_ref(v_inst_414_);
v___x_425_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_426_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
lean_inc(v_toBind_422_);
v___f_427_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 13, 12);
lean_closure_set(v___f_427_, 0, v___x_426_);
lean_closure_set(v___f_427_, 1, v_kind_419_);
lean_closure_set(v___f_427_, 2, v_declName_420_);
lean_closure_set(v___f_427_, 3, v___x_425_);
lean_closure_set(v___f_427_, 4, v_modifyEnv_424_);
lean_closure_set(v___f_427_, 5, v_inst_413_);
lean_closure_set(v___f_427_, 6, v_inst_415_);
lean_closure_set(v___f_427_, 7, v_inst_417_);
lean_closure_set(v___f_427_, 8, v_inst_418_);
lean_closure_set(v___f_427_, 9, v_toBind_422_);
lean_closure_set(v___f_427_, 10, v_inst_416_);
lean_closure_set(v___f_427_, 11, v_toApplicative_421_);
v___x_428_ = lean_apply_4(v_toBind_422_, lean_box(0), lean_box(0), v_getEnv_423_, v___f_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_kind_436_, lean_object* v_declName_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_recordIndirectModUse___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_inst_433_, v_inst_434_, v_inst_435_, v_kind_436_, v_declName_437_);
return v___x_438_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_module_441_; uint8_t v_isExported_442_; uint8_t v_isMeta_443_; lean_object* v_module_444_; uint8_t v_isExported_445_; uint8_t v_isMeta_446_; uint8_t v___y_448_; uint8_t v___x_449_; 
v_module_441_ = lean_ctor_get(v_x_439_, 0);
v_isExported_442_ = lean_ctor_get_uint8(v_x_439_, sizeof(void*)*1);
v_isMeta_443_ = lean_ctor_get_uint8(v_x_439_, sizeof(void*)*1 + 1);
v_module_444_ = lean_ctor_get(v_x_440_, 0);
v_isExported_445_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*1);
v_isMeta_446_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*1 + 1);
v___x_449_ = lean_name_eq(v_module_441_, v_module_444_);
if (v___x_449_ == 0)
{
return v___x_449_;
}
else
{
if (v_isExported_442_ == 0)
{
if (v_isExported_445_ == 0)
{
v___y_448_ = v___x_449_;
goto v___jp_447_;
}
else
{
return v_isExported_442_;
}
}
else
{
v___y_448_ = v_isExported_445_;
goto v___jp_447_;
}
}
v___jp_447_:
{
if (v___y_448_ == 0)
{
return v___y_448_;
}
else
{
if (v_isMeta_443_ == 0)
{
if (v_isMeta_446_ == 0)
{
return v___y_448_;
}
else
{
return v_isMeta_443_;
}
}
else
{
return v_isMeta_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Lean_instBEqExtraModUse_beq(v_x_450_, v_x_451_);
lean_dec_ref(v_x_451_);
lean_dec_ref(v_x_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_456_){
_start:
{
lean_object* v_module_457_; uint8_t v_isExported_458_; uint8_t v_isMeta_459_; uint64_t v___y_461_; uint64_t v___y_462_; uint64_t v___x_468_; uint64_t v___y_470_; 
v_module_457_ = lean_ctor_get(v_x_456_, 0);
v_isExported_458_ = lean_ctor_get_uint8(v_x_456_, sizeof(void*)*1);
v_isMeta_459_ = lean_ctor_get_uint8(v_x_456_, sizeof(void*)*1 + 1);
v___x_468_ = 0ULL;
if (lean_obj_tag(v_module_457_) == 0)
{
uint64_t v___x_474_; 
v___x_474_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_470_ = v___x_474_;
goto v___jp_469_;
}
else
{
uint64_t v_hash_475_; 
v_hash_475_ = lean_ctor_get_uint64(v_module_457_, sizeof(void*)*2);
v___y_470_ = v_hash_475_;
goto v___jp_469_;
}
v___jp_460_:
{
uint64_t v___x_463_; 
v___x_463_ = lean_uint64_mix_hash(v___y_461_, v___y_462_);
if (v_isMeta_459_ == 0)
{
uint64_t v___x_464_; uint64_t v___x_465_; 
v___x_464_ = 13ULL;
v___x_465_ = lean_uint64_mix_hash(v___x_463_, v___x_464_);
return v___x_465_;
}
else
{
uint64_t v___x_466_; uint64_t v___x_467_; 
v___x_466_ = 11ULL;
v___x_467_ = lean_uint64_mix_hash(v___x_463_, v___x_466_);
return v___x_467_;
}
}
v___jp_469_:
{
uint64_t v___x_471_; 
v___x_471_ = lean_uint64_mix_hash(v___x_468_, v___y_470_);
if (v_isExported_458_ == 0)
{
uint64_t v___x_472_; 
v___x_472_ = 13ULL;
v___y_461_ = v___x_471_;
v___y_462_ = v___x_472_;
goto v___jp_460_;
}
else
{
uint64_t v___x_473_; 
v___x_473_ = 11ULL;
v___y_461_ = v___x_471_;
v___y_462_ = v___x_473_;
goto v___jp_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_476_){
_start:
{
uint64_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lean_instHashableExtraModUse_hash(v_x_476_);
lean_dec_ref(v_x_476_);
v_r_478_ = lean_box_uint64(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_nat_to_int(v_a_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(10u);
v___x_497_ = lean_nat_to_int(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(14u);
v___x_505_ = lean_nat_to_int(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_511_ = lean_string_length(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_513_ = lean_nat_to_int(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_518_){
_start:
{
lean_object* v_module_519_; uint8_t v_isExported_520_; uint8_t v_isMeta_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_module_519_ = lean_ctor_get(v_x_518_, 0);
lean_inc(v_module_519_);
v_isExported_520_ = lean_ctor_get_uint8(v_x_518_, sizeof(void*)*1);
v_isMeta_521_ = lean_ctor_get_uint8(v_x_518_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_518_);
v___x_522_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_523_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_524_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Lean_Name_reprPrec(v_module_519_, v___x_525_);
v___x_527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_523_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_box(1);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_522_);
v___x_538_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_539_ = l_Bool_repr___redArg(v_isExported_520_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_528_);
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_537_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_531_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_533_);
v___x_545_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_522_);
v___x_548_ = l_Bool_repr___redArg(v_isMeta_521_);
v___x_549_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_524_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*1, v___x_528_);
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_547_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_553_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_551_);
v___x_555_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_552_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*1, v___x_528_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_559_, lean_object* v_prec_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_562_, lean_object* v_prec_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_instReprExtraModUse_repr(v_x_562_, v_prec_563_);
lean_dec(v_prec_563_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_567_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__0);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1___closed__1);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_entries_576_, uint8_t v_x_577_){
_start:
{
if (v_x_577_ == 2)
{
lean_object* v___x_578_; 
v___x_578_ = lean_array_mk(v_entries_576_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; 
lean_dec(v_entries_576_);
v___x_579_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_));
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_entries_582_, lean_object* v_x_583_){
_start:
{
uint8_t v_x_473__boxed_584_; lean_object* v_res_585_; 
v_x_473__boxed_584_ = lean_unbox(v_x_583_);
v_res_585_ = l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(v_x_580_, v_x_581_, v_entries_582_, v_x_473__boxed_584_);
lean_dec_ref(v_x_581_);
lean_dec_ref(v_x_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object* v_es_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_array_mk(v_es_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__1(lean_box(0));
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed(lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(v_x_591_);
lean_dec_ref(v_x_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_ks_597_; lean_object* v_vs_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_622_; 
v_ks_597_ = lean_ctor_get(v_x_593_, 0);
v_vs_598_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_622_ == 0)
{
v___x_600_ = v_x_593_;
v_isShared_601_ = v_isSharedCheck_622_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_vs_598_);
lean_inc(v_ks_597_);
lean_dec(v_x_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_622_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_array_get_size(v_ks_597_);
v___x_603_ = lean_nat_dec_lt(v_x_594_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_x_594_);
v___x_604_ = lean_array_push(v_ks_597_, v_x_595_);
v___x_605_ = lean_array_push(v_vs_598_, v_x_596_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_605_);
lean_ctor_set(v___x_600_, 0, v___x_604_);
v___x_607_ = v___x_600_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v_k_x27_609_; uint8_t v___x_610_; 
v_k_x27_609_ = lean_array_fget_borrowed(v_ks_597_, v_x_594_);
v___x_610_ = l_Lean_instBEqExtraModUse_beq(v_x_595_, v_k_x27_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_612_; 
if (v_isShared_601_ == 0)
{
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_ks_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_vs_598_);
v___x_612_ = v_reuseFailAlloc_616_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_x_594_, v___x_613_);
lean_dec(v_x_594_);
v_x_593_ = v___x_612_;
v_x_594_ = v___x_614_;
goto _start;
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_array_fset(v_ks_597_, v_x_594_, v_x_595_);
v___x_618_ = lean_array_fset(v_vs_598_, v_x_594_, v_x_596_);
lean_dec(v_x_594_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_618_);
lean_ctor_set(v___x_600_, 0, v___x_617_);
v___x_620_ = v___x_600_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_623_, lean_object* v_k_624_, lean_object* v_v_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_623_, v___x_626_, v_k_624_, v_v_625_);
return v___x_627_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; 
v___x_628_ = ((size_t)5ULL);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_shift_left(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_633_ = lean_usize_sub(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_635_, size_t v_x_636_, size_t v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v_es_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; size_t v___x_644_; lean_object* v_j_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_es_640_ = lean_ctor_get(v_x_635_, 0);
v___x_641_ = ((size_t)5ULL);
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1);
v___x_644_ = lean_usize_land(v_x_636_, v___x_643_);
v_j_645_ = lean_usize_to_nat(v___x_644_);
v___x_646_ = lean_array_get_size(v_es_640_);
v___x_647_ = lean_nat_dec_lt(v_j_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v_j_645_);
lean_dec(v_x_639_);
lean_dec_ref(v_x_638_);
return v_x_635_;
}
else
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_684_; 
lean_inc_ref(v_es_640_);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_x_635_, 0);
lean_dec(v_unused_685_);
v___x_649_ = v_x_635_;
v_isShared_650_ = v_isSharedCheck_684_;
goto v_resetjp_648_;
}
else
{
lean_dec(v_x_635_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_684_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_v_651_; lean_object* v___x_652_; lean_object* v_xs_x27_653_; lean_object* v___y_655_; 
v_v_651_ = lean_array_fget(v_es_640_, v_j_645_);
v___x_652_ = lean_box(0);
v_xs_x27_653_ = lean_array_fset(v_es_640_, v_j_645_, v___x_652_);
switch(lean_obj_tag(v_v_651_))
{
case 0:
{
lean_object* v_key_660_; lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_671_; 
v_key_660_ = lean_ctor_get(v_v_651_, 0);
v_val_661_ = lean_ctor_get(v_v_651_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_v_651_);
if (v_isSharedCheck_671_ == 0)
{
v___x_663_ = v_v_651_;
v_isShared_664_ = v_isSharedCheck_671_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_inc(v_key_660_);
lean_dec(v_v_651_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_671_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
uint8_t v___x_665_; 
v___x_665_ = l_Lean_instBEqExtraModUse_beq(v_x_638_, v_key_660_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_del_object(v___x_663_);
v___x_666_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_660_, v_val_661_, v_x_638_, v_x_639_);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
v___y_655_ = v___x_667_;
goto v___jp_654_;
}
else
{
lean_object* v___x_669_; 
lean_dec(v_val_661_);
lean_dec(v_key_660_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_x_639_);
lean_ctor_set(v___x_663_, 0, v_x_638_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_x_638_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_x_639_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
v___y_655_ = v___x_669_;
goto v___jp_654_;
}
}
}
}
case 1:
{
lean_object* v_node_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
v_node_672_ = lean_ctor_get(v_v_651_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_v_651_);
if (v_isSharedCheck_682_ == 0)
{
v___x_674_ = v_v_651_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_node_672_);
lean_dec(v_v_651_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_676_ = lean_usize_shift_right(v_x_636_, v___x_641_);
v___x_677_ = lean_usize_add(v_x_637_, v___x_642_);
v___x_678_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_672_, v___x_676_, v___x_677_, v_x_638_, v_x_639_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_678_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v___y_655_ = v___x_680_;
goto v___jp_654_;
}
}
}
default: 
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_x_638_);
lean_ctor_set(v___x_683_, 1, v_x_639_);
v___y_655_ = v___x_683_;
goto v___jp_654_;
}
}
v___jp_654_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_array_fset(v_xs_x27_653_, v_j_645_, v___y_655_);
lean_dec(v_j_645_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_656_);
v___x_658_ = v___x_649_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v_ks_686_; lean_object* v_vs_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_707_; 
v_ks_686_ = lean_ctor_get(v_x_635_, 0);
v_vs_687_ = lean_ctor_get(v_x_635_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_707_ == 0)
{
v___x_689_ = v_x_635_;
v_isShared_690_ = v_isSharedCheck_707_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_vs_687_);
lean_inc(v_ks_686_);
lean_dec(v_x_635_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_707_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_ks_686_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_vs_687_);
v___x_692_ = v_reuseFailAlloc_706_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v_newNode_693_; uint8_t v___y_695_; size_t v___x_701_; uint8_t v___x_702_; 
v_newNode_693_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_692_, v_x_638_, v_x_639_);
v___x_701_ = ((size_t)7ULL);
v___x_702_ = lean_usize_dec_le(v___x_701_, v_x_637_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_693_);
v___x_704_ = lean_unsigned_to_nat(4u);
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_704_);
lean_dec(v___x_703_);
v___y_695_ = v___x_705_;
goto v___jp_694_;
}
else
{
v___y_695_ = v___x_702_;
goto v___jp_694_;
}
v___jp_694_:
{
if (v___y_695_ == 0)
{
lean_object* v_ks_696_; lean_object* v_vs_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_ks_696_ = lean_ctor_get(v_newNode_693_, 0);
lean_inc_ref(v_ks_696_);
v_vs_697_ = lean_ctor_get(v_newNode_693_, 1);
lean_inc_ref(v_vs_697_);
lean_dec_ref(v_newNode_693_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2);
v___x_700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_637_, v_ks_696_, v_vs_697_, v___x_698_, v___x_699_);
lean_dec_ref(v_vs_697_);
lean_dec_ref(v_ks_696_);
return v___x_700_;
}
else
{
return v_newNode_693_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_708_, lean_object* v_keys_709_, lean_object* v_vals_710_, lean_object* v_i_711_, lean_object* v_entries_712_){
_start:
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_array_get_size(v_keys_709_);
v___x_714_ = lean_nat_dec_lt(v_i_711_, v___x_713_);
if (v___x_714_ == 0)
{
lean_dec(v_i_711_);
return v_entries_712_;
}
else
{
lean_object* v_k_715_; lean_object* v_v_716_; uint64_t v___x_717_; size_t v_h_718_; size_t v___x_719_; lean_object* v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; size_t v_h_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_k_715_ = lean_array_fget_borrowed(v_keys_709_, v_i_711_);
v_v_716_ = lean_array_fget_borrowed(v_vals_710_, v_i_711_);
v___x_717_ = l_Lean_instHashableExtraModUse_hash(v_k_715_);
v_h_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = ((size_t)5ULL);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_sub(v_depth_708_, v___x_721_);
v___x_723_ = lean_usize_mul(v___x_719_, v___x_722_);
v_h_724_ = lean_usize_shift_right(v_h_718_, v___x_723_);
v___x_725_ = lean_nat_add(v_i_711_, v___x_720_);
lean_dec(v_i_711_);
lean_inc(v_v_716_);
lean_inc(v_k_715_);
v___x_726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_712_, v_h_724_, v_depth_708_, v_k_715_, v_v_716_);
v_i_711_ = v___x_725_;
v_entries_712_ = v___x_726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_728_, lean_object* v_keys_729_, lean_object* v_vals_730_, lean_object* v_i_731_, lean_object* v_entries_732_){
_start:
{
size_t v_depth_boxed_733_; lean_object* v_res_734_; 
v_depth_boxed_733_ = lean_unbox_usize(v_depth_728_);
lean_dec(v_depth_728_);
v_res_734_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_733_, v_keys_729_, v_vals_730_, v_i_731_, v_entries_732_);
lean_dec_ref(v_vals_730_);
lean_dec_ref(v_keys_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
size_t v_x_585__boxed_740_; size_t v_x_586__boxed_741_; lean_object* v_res_742_; 
v_x_585__boxed_740_ = lean_unbox_usize(v_x_736_);
lean_dec(v_x_736_);
v_x_586__boxed_741_ = lean_unbox_usize(v_x_737_);
lean_dec(v_x_737_);
v_res_742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_735_, v_x_585__boxed_740_, v_x_586__boxed_741_, v_x_738_, v_x_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
uint64_t v___x_746_; size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_746_ = l_Lean_instHashableExtraModUse_hash(v_x_744_);
v___x_747_ = lean_uint64_to_usize(v___x_746_);
v___x_748_ = ((size_t)1ULL);
v___x_749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_743_, v___x_747_, v___x_748_, v_x_744_, v_x_745_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(lean_object* v_m_750_, lean_object* v_k_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
v___x_753_ = l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2___redArg(v_m_750_, v_k_751_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_754_, lean_object* v_i_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_keys_754_);
v___x_758_ = lean_nat_dec_lt(v_i_755_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_i_755_);
return v___x_758_;
}
else
{
lean_object* v_k_x27_759_; uint8_t v___x_760_; 
v_k_x27_759_ = lean_array_fget_borrowed(v_keys_754_, v_i_755_);
v___x_760_ = l_Lean_instBEqExtraModUse_beq(v_k_756_, v_k_x27_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_i_755_, v___x_761_);
lean_dec(v_i_755_);
v_i_755_ = v___x_762_;
goto _start;
}
else
{
lean_dec(v_i_755_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_764_, lean_object* v_i_765_, lean_object* v_k_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_764_, v_i_765_, v_k_766_);
lean_dec_ref(v_k_766_);
lean_dec_ref(v_keys_764_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_769_, size_t v_x_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
lean_object* v_es_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v_j_777_; lean_object* v___x_778_; 
v_es_772_ = lean_ctor_get(v_x_769_, 0);
lean_inc_ref(v_es_772_);
lean_dec_ref(v_x_769_);
v___x_773_ = lean_box(2);
v___x_774_ = ((size_t)5ULL);
v___x_775_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1);
v___x_776_ = lean_usize_land(v_x_770_, v___x_775_);
v_j_777_ = lean_usize_to_nat(v___x_776_);
v___x_778_ = lean_array_get(v___x_773_, v_es_772_, v_j_777_);
lean_dec(v_j_777_);
lean_dec_ref(v_es_772_);
switch(lean_obj_tag(v___x_778_))
{
case 0:
{
lean_object* v_key_779_; uint8_t v___x_780_; 
v_key_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_key_779_);
lean_dec_ref(v___x_778_);
v___x_780_ = l_Lean_instBEqExtraModUse_beq(v_x_771_, v_key_779_);
lean_dec(v_key_779_);
return v___x_780_;
}
case 1:
{
lean_object* v_node_781_; size_t v___x_782_; 
v_node_781_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_node_781_);
lean_dec_ref(v___x_778_);
v___x_782_ = lean_usize_shift_right(v_x_770_, v___x_774_);
v_x_769_ = v_node_781_;
v_x_770_ = v___x_782_;
goto _start;
}
default: 
{
uint8_t v___x_784_; 
v___x_784_ = 0;
return v___x_784_;
}
}
}
else
{
lean_object* v_ks_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_ks_785_ = lean_ctor_get(v_x_769_, 0);
lean_inc_ref(v_ks_785_);
lean_dec_ref(v_x_769_);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_785_, v___x_786_, v_x_771_);
lean_dec_ref(v_ks_785_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
size_t v_x_783__boxed_791_; uint8_t v_res_792_; lean_object* v_r_793_; 
v_x_783__boxed_791_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_788_, v_x_783__boxed_791_, v_x_790_);
lean_dec_ref(v_x_790_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
uint64_t v___x_796_; size_t v___x_797_; uint8_t v___x_798_; 
v___x_796_ = l_Lean_instHashableExtraModUse_hash(v_x_795_);
v___x_797_ = lean_uint64_to_usize(v___x_796_);
v___x_798_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_794_, v___x_797_, v_x_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg(v_x_799_, v_x_800_);
lean_dec_ref(v_x_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_));
v___x_828_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2____boxed(lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_();
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg(v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0(v_00_u03b2_835_, v_x_836_, v_x_837_);
lean_dec_ref(v_x_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2___redArg(v_x_841_, v_x_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_845_, lean_object* v_x_846_, size_t v_x_847_, lean_object* v_x_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_846_, v_x_847_, v_x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
size_t v_x_932__boxed_854_; uint8_t v_res_855_; lean_object* v_r_856_; 
v_x_932__boxed_854_ = lean_unbox_usize(v_x_852_);
lean_dec(v_x_852_);
v_res_855_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_850_, v_x_851_, v_x_932__boxed_854_, v_x_853_);
lean_dec_ref(v_x_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, size_t v_x_859_, size_t v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_858_, v_x_859_, v_x_860_, v_x_861_, v_x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
size_t v_x_943__boxed_870_; size_t v_x_944__boxed_871_; lean_object* v_res_872_; 
v_x_943__boxed_870_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_x_944__boxed_871_ = lean_unbox_usize(v_x_867_);
lean_dec(v_x_867_);
v_res_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_864_, v_x_865_, v_x_943__boxed_870_, v_x_944__boxed_871_, v_x_868_, v_x_869_);
return v_res_872_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_873_, lean_object* v_keys_874_, lean_object* v_vals_875_, lean_object* v_heq_876_, lean_object* v_i_877_, lean_object* v_k_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_874_, v_i_877_, v_k_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_880_, lean_object* v_keys_881_, lean_object* v_vals_882_, lean_object* v_heq_883_, lean_object* v_i_884_, lean_object* v_k_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_880_, v_keys_881_, v_vals_882_, v_heq_883_, v_i_884_, v_k_885_);
lean_dec_ref(v_k_885_);
lean_dec_ref(v_vals_882_);
lean_dec_ref(v_keys_881_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_888_, lean_object* v_n_889_, lean_object* v_k_890_, lean_object* v_v_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_889_, v_k_890_, v_v_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_893_, size_t v_depth_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_heq_897_, lean_object* v_i_898_, lean_object* v_entries_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_894_, v_keys_895_, v_vals_896_, v_i_898_, v_entries_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_901_, lean_object* v_depth_902_, lean_object* v_keys_903_, lean_object* v_vals_904_, lean_object* v_heq_905_, lean_object* v_i_906_, lean_object* v_entries_907_){
_start:
{
size_t v_depth_boxed_908_; lean_object* v_res_909_; 
v_depth_boxed_908_ = lean_unbox_usize(v_depth_902_);
lean_dec(v_depth_902_);
v_res_909_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_901_, v_depth_boxed_908_, v_keys_903_, v_vals_904_, v_heq_905_, v_i_906_, v_entries_907_);
lean_dec_ref(v_vals_904_);
lean_dec_ref(v_keys_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_911_, v_x_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_917_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_918_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_920_ = lean_box(0);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_922_, lean_object* v_modIdx_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_925_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_926_ = 0;
v___x_927_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_924_, v___x_925_, v_env_922_, v_modIdx_923_, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_928_, lean_object* v_modIdx_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_getExtraModUses(v_env_928_, v_modIdx_929_);
lean_dec(v_modIdx_929_);
lean_dec_ref(v_env_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_931_, lean_object* v_b_932_){
_start:
{
if (lean_obj_tag(v_as_x27_931_) == 0)
{
return v_b_932_;
}
else
{
lean_object* v_head_933_; lean_object* v_tail_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_head_933_ = lean_ctor_get(v_as_x27_931_, 0);
lean_inc(v_head_933_);
v_tail_934_ = lean_ctor_get(v_as_x27_931_, 1);
lean_inc(v_tail_934_);
lean_dec_ref(v_as_x27_931_);
v___x_935_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_936_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_937_ = lean_box(1);
v___x_938_ = lean_box(0);
lean_inc_ref(v_b_932_);
v___x_939_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_935_, v___x_936_, v_b_932_, v___x_937_, v___x_938_);
v___x_940_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2__spec__0___redArg(v___x_939_, v_head_933_);
if (v___x_940_ == 0)
{
lean_object* v_toEnvExtension_941_; lean_object* v_asyncMode_942_; lean_object* v___x_943_; 
v_toEnvExtension_941_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_toEnvExtension_941_);
v_asyncMode_942_ = lean_ctor_get(v_toEnvExtension_941_, 2);
lean_inc(v_asyncMode_942_);
lean_dec_ref(v_toEnvExtension_941_);
v___x_943_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_936_, v_b_932_, v_head_933_, v_asyncMode_942_, v___x_938_);
lean_dec(v_asyncMode_942_);
v_as_x27_931_ = v_tail_934_;
v_b_932_ = v___x_943_;
goto _start;
}
else
{
lean_dec(v_head_933_);
v_as_x27_931_ = v_tail_934_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_946_, lean_object* v_dest_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_948_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_949_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_950_ = lean_box(1);
v___x_951_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_948_, v___x_949_, v_src_946_, v___x_950_);
v___x_952_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_951_, v_dest_947_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_953_, lean_object* v_as_x27_954_, lean_object* v_b_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_954_, v_b_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_958_, lean_object* v_as_x27_959_, lean_object* v_b_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_958_, v_as_x27_959_, v_b_960_, v_a_961_);
lean_dec(v_as_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_963_, lean_object* v_entry_964_, lean_object* v___x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v_toEnvExtension_967_; lean_object* v_asyncMode_968_; lean_object* v___x_969_; 
v_toEnvExtension_967_ = lean_ctor_get(v___x_963_, 0);
v_asyncMode_968_ = lean_ctor_get(v_toEnvExtension_967_, 2);
lean_inc(v_asyncMode_968_);
v___x_969_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_963_, v_x_966_, v_entry_964_, v_asyncMode_968_, v___x_965_);
lean_dec(v_asyncMode_968_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_modifyEnv_989_, lean_object* v___f_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_cls_995_, lean_object* v_toBind_996_, lean_object* v___f_997_, lean_object* v_mod_998_, lean_object* v_hint_999_, uint8_t v_isMeta_1000_, uint8_t v_isExporting_1001_, uint8_t v_____do__lift_1002_){
_start:
{
lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1010_; lean_object* v___y_1011_; 
if (v_____do__lift_1002_ == 0)
{
lean_object* v___x_1023_; 
lean_dec(v_hint_999_);
lean_dec(v_mod_998_);
lean_dec(v___f_997_);
lean_dec(v_toBind_996_);
lean_dec(v_cls_995_);
lean_dec(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec_ref(v_inst_992_);
lean_dec_ref(v_inst_991_);
v___x_1023_ = lean_apply_1(v_modifyEnv_989_, v___f_990_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; lean_object* v___y_1026_; 
lean_dec_ref(v___f_990_);
lean_dec(v_modifyEnv_989_);
v___x_1024_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
if (v_isExporting_1001_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12));
v___y_1026_ = v___x_1033_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13));
v___y_1026_ = v___x_1034_;
goto v___jp_1025_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = l_Lean_stringToMessageData(v___y_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
if (v_isMeta_1000_ == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10));
v___y_1010_ = v___x_1030_;
v___y_1011_ = v___x_1031_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11));
v___y_1010_ = v___x_1030_;
v___y_1011_ = v___x_1032_;
goto v___jp_1009_;
}
}
}
v___jp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_1004_);
lean_ctor_set(v___x_1006_, 1, v___y_1005_);
v___x_1007_ = l_Lean_addTrace___redArg(v_inst_991_, v_inst_992_, v_inst_993_, v_inst_994_, v_cls_995_, v___x_1006_);
v___x_1008_ = lean_apply_4(v_toBind_996_, lean_box(0), lean_box(0), v___x_1007_, v___f_997_);
return v___x_1008_;
}
v___jp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1012_ = l_Lean_stringToMessageData(v___y_1011_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___y_1010_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_ofName(v_mod_998_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_Name_isAnonymous(v_hint_999_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
v___x_1020_ = l_Lean_MessageData_ofName(v_hint_999_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___y_1004_ = v___x_1017_;
v___y_1005_ = v___x_1021_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1022_; 
lean_dec(v_hint_999_);
v___x_1022_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
v___y_1004_ = v___x_1017_;
v___y_1005_ = v___x_1022_;
goto v___jp_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_modifyEnv_1035_, lean_object* v___f_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_cls_1041_, lean_object* v_toBind_1042_, lean_object* v___f_1043_, lean_object* v_mod_1044_, lean_object* v_hint_1045_, lean_object* v_isMeta_1046_, lean_object* v_isExporting_1047_, lean_object* v_____do__lift_1048_){
_start:
{
uint8_t v_isMeta_boxed_1049_; uint8_t v_isExporting_boxed_1050_; uint8_t v_____do__lift_850__boxed_1051_; lean_object* v_res_1052_; 
v_isMeta_boxed_1049_ = lean_unbox(v_isMeta_1046_);
v_isExporting_boxed_1050_ = lean_unbox(v_isExporting_1047_);
v_____do__lift_850__boxed_1051_ = lean_unbox(v_____do__lift_1048_);
v_res_1052_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_modifyEnv_1035_, v___f_1036_, v_inst_1037_, v_inst_1038_, v_inst_1039_, v_inst_1040_, v_cls_1041_, v_toBind_1042_, v___f_1043_, v_mod_1044_, v_hint_1045_, v_isMeta_boxed_1049_, v_isExporting_boxed_1050_, v_____do__lift_850__boxed_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v___x_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_entry_1056_, lean_object* v_modifyEnv_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_toBind_1062_, lean_object* v_mod_1063_, lean_object* v_hint_1064_, uint8_t v_isMeta_1065_, uint8_t v_isExporting_1066_, lean_object* v_inst_1067_, lean_object* v_toApplicative_1068_, lean_object* v_____do__lift_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1070_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1071_ = lean_box(1);
v___x_1072_ = lean_box(0);
v___x_1073_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1053_, v___x_1070_, v_____do__lift_1069_, v___x_1071_, v___x_1072_);
lean_inc_ref(v_entry_1056_);
v___x_1074_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1054_, v___x_1055_, v___x_1073_, v_entry_1056_);
if (v___x_1074_ == 0)
{
lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v_cls_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_toApplicative_1068_);
v___f_1075_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1075_, 0, v___x_1070_);
lean_closure_set(v___f_1075_, 1, v_entry_1056_);
lean_closure_set(v___f_1075_, 2, v___x_1072_);
lean_inc_ref(v___f_1075_);
lean_inc(v_modifyEnv_1057_);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1076_, 0, v_modifyEnv_1057_);
lean_closure_set(v___f_1076_, 1, v___f_1075_);
v_cls_1077_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
v___x_1078_ = lean_box(v_isMeta_1065_);
v___x_1079_ = lean_box(v_isExporting_1066_);
lean_inc(v_toBind_1062_);
lean_inc_ref(v_inst_1059_);
lean_inc_ref(v_inst_1058_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1080_, 0, v_modifyEnv_1057_);
lean_closure_set(v___f_1080_, 1, v___f_1075_);
lean_closure_set(v___f_1080_, 2, v_inst_1058_);
lean_closure_set(v___f_1080_, 3, v_inst_1059_);
lean_closure_set(v___f_1080_, 4, v_inst_1060_);
lean_closure_set(v___f_1080_, 5, v_inst_1061_);
lean_closure_set(v___f_1080_, 6, v_cls_1077_);
lean_closure_set(v___f_1080_, 7, v_toBind_1062_);
lean_closure_set(v___f_1080_, 8, v___f_1076_);
lean_closure_set(v___f_1080_, 9, v_mod_1063_);
lean_closure_set(v___f_1080_, 10, v_hint_1064_);
lean_closure_set(v___f_1080_, 11, v___x_1078_);
lean_closure_set(v___f_1080_, 12, v___x_1079_);
v___x_1081_ = l_Lean_isTracingEnabledFor___redArg(v_inst_1058_, v_inst_1059_, v_inst_1067_, v_cls_1077_);
v___x_1082_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1081_, v___f_1080_);
return v___x_1082_;
}
else
{
lean_object* v_toPure_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v_inst_1067_);
lean_dec(v_hint_1064_);
lean_dec(v_mod_1063_);
lean_dec(v_toBind_1062_);
lean_dec(v_inst_1061_);
lean_dec_ref(v_inst_1060_);
lean_dec_ref(v_inst_1059_);
lean_dec_ref(v_inst_1058_);
lean_dec(v_modifyEnv_1057_);
lean_dec_ref(v_entry_1056_);
v_toPure_1083_ = lean_ctor_get(v_toApplicative_1068_, 1);
lean_inc(v_toPure_1083_);
lean_dec_ref(v_toApplicative_1068_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_apply_2(v_toPure_1083_, lean_box(0), v___x_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1086_ = _args[0];
lean_object* v___x_1087_ = _args[1];
lean_object* v___x_1088_ = _args[2];
lean_object* v_entry_1089_ = _args[3];
lean_object* v_modifyEnv_1090_ = _args[4];
lean_object* v_inst_1091_ = _args[5];
lean_object* v_inst_1092_ = _args[6];
lean_object* v_inst_1093_ = _args[7];
lean_object* v_inst_1094_ = _args[8];
lean_object* v_toBind_1095_ = _args[9];
lean_object* v_mod_1096_ = _args[10];
lean_object* v_hint_1097_ = _args[11];
lean_object* v_isMeta_1098_ = _args[12];
lean_object* v_isExporting_1099_ = _args[13];
lean_object* v_inst_1100_ = _args[14];
lean_object* v_toApplicative_1101_ = _args[15];
lean_object* v_____do__lift_1102_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1103_; uint8_t v_isExporting_boxed_1104_; lean_object* v_res_1105_; 
v_isMeta_boxed_1103_ = lean_unbox(v_isMeta_1098_);
v_isExporting_boxed_1104_ = lean_unbox(v_isExporting_1099_);
v_res_1105_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v___x_1086_, v___x_1087_, v___x_1088_, v_entry_1089_, v_modifyEnv_1090_, v_inst_1091_, v_inst_1092_, v_inst_1093_, v_inst_1094_, v_toBind_1095_, v_mod_1096_, v_hint_1097_, v_isMeta_boxed_1103_, v_isExporting_boxed_1104_, v_inst_1100_, v_toApplicative_1101_, v_____do__lift_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(lean_object* v_mod_1106_, uint8_t v_isMeta_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v_modifyEnv_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_toBind_1116_, lean_object* v_hint_1117_, lean_object* v_inst_1118_, lean_object* v_toApplicative_1119_, lean_object* v_getEnv_1120_, lean_object* v_____do__lift_1121_){
_start:
{
uint8_t v_isExporting_1122_; lean_object* v_entry_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; 
v_isExporting_1122_ = lean_ctor_get_uint8(v_____do__lift_1121_, sizeof(void*)*8);
lean_inc(v_mod_1106_);
v_entry_1123_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1123_, 0, v_mod_1106_);
lean_ctor_set_uint8(v_entry_1123_, sizeof(void*)*1, v_isExporting_1122_);
lean_ctor_set_uint8(v_entry_1123_, sizeof(void*)*1 + 1, v_isMeta_1107_);
v___x_1124_ = lean_box(v_isMeta_1107_);
v___x_1125_ = lean_box(v_isExporting_1122_);
lean_inc(v_toBind_1116_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 17, 16);
lean_closure_set(v___f_1126_, 0, v___x_1108_);
lean_closure_set(v___f_1126_, 1, v___x_1109_);
lean_closure_set(v___f_1126_, 2, v___x_1110_);
lean_closure_set(v___f_1126_, 3, v_entry_1123_);
lean_closure_set(v___f_1126_, 4, v_modifyEnv_1111_);
lean_closure_set(v___f_1126_, 5, v_inst_1112_);
lean_closure_set(v___f_1126_, 6, v_inst_1113_);
lean_closure_set(v___f_1126_, 7, v_inst_1114_);
lean_closure_set(v___f_1126_, 8, v_inst_1115_);
lean_closure_set(v___f_1126_, 9, v_toBind_1116_);
lean_closure_set(v___f_1126_, 10, v_mod_1106_);
lean_closure_set(v___f_1126_, 11, v_hint_1117_);
lean_closure_set(v___f_1126_, 12, v___x_1124_);
lean_closure_set(v___f_1126_, 13, v___x_1125_);
lean_closure_set(v___f_1126_, 14, v_inst_1118_);
lean_closure_set(v___f_1126_, 15, v_toApplicative_1119_);
v___x_1127_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v_getEnv_1120_, v___f_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3___boxed(lean_object* v_mod_1128_, lean_object* v_isMeta_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v_modifyEnv_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_toBind_1138_, lean_object* v_hint_1139_, lean_object* v_inst_1140_, lean_object* v_toApplicative_1141_, lean_object* v_getEnv_1142_, lean_object* v_____do__lift_1143_){
_start:
{
uint8_t v_isMeta_boxed_1144_; lean_object* v_res_1145_; 
v_isMeta_boxed_1144_ = lean_unbox(v_isMeta_1129_);
v_res_1145_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3(v_mod_1128_, v_isMeta_boxed_1144_, v___x_1130_, v___x_1131_, v___x_1132_, v_modifyEnv_1133_, v_inst_1134_, v_inst_1135_, v_inst_1136_, v_inst_1137_, v_toBind_1138_, v_hint_1139_, v_inst_1140_, v_toApplicative_1141_, v_getEnv_1142_, v_____do__lift_1143_);
lean_dec_ref(v_____do__lift_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_mod_1152_, uint8_t v_isMeta_1153_, lean_object* v_hint_1154_){
_start:
{
lean_object* v_toApplicative_1155_; lean_object* v_toBind_1156_; lean_object* v_getEnv_1157_; lean_object* v_modifyEnv_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v_toApplicative_1155_ = lean_ctor_get(v_inst_1146_, 0);
lean_inc_ref(v_toApplicative_1155_);
v_toBind_1156_ = lean_ctor_get(v_inst_1146_, 1);
lean_inc(v_toBind_1156_);
v_getEnv_1157_ = lean_ctor_get(v_inst_1147_, 0);
lean_inc(v_getEnv_1157_);
v_modifyEnv_1158_ = lean_ctor_get(v_inst_1147_, 1);
lean_inc(v_modifyEnv_1158_);
lean_dec_ref(v_inst_1147_);
v___x_1159_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1160_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1161_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1162_ = lean_box(v_isMeta_1153_);
lean_inc(v_getEnv_1157_);
lean_inc(v_toBind_1156_);
v___f_1163_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_1163_, 0, v_mod_1152_);
lean_closure_set(v___f_1163_, 1, v___x_1162_);
lean_closure_set(v___f_1163_, 2, v___x_1161_);
lean_closure_set(v___f_1163_, 3, v___x_1159_);
lean_closure_set(v___f_1163_, 4, v___x_1160_);
lean_closure_set(v___f_1163_, 5, v_modifyEnv_1158_);
lean_closure_set(v___f_1163_, 6, v_inst_1146_);
lean_closure_set(v___f_1163_, 7, v_inst_1148_);
lean_closure_set(v___f_1163_, 8, v_inst_1150_);
lean_closure_set(v___f_1163_, 9, v_inst_1151_);
lean_closure_set(v___f_1163_, 10, v_toBind_1156_);
lean_closure_set(v___f_1163_, 11, v_hint_1154_);
lean_closure_set(v___f_1163_, 12, v_inst_1149_);
lean_closure_set(v___f_1163_, 13, v_toApplicative_1155_);
lean_closure_set(v___f_1163_, 14, v_getEnv_1157_);
v___x_1164_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v_getEnv_1157_, v___f_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_mod_1171_, lean_object* v_isMeta_1172_, lean_object* v_hint_1173_){
_start:
{
uint8_t v_isMeta_boxed_1174_; lean_object* v_res_1175_; 
v_isMeta_boxed_1174_ = lean_unbox(v_isMeta_1172_);
v_res_1175_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1165_, v_inst_1166_, v_inst_1167_, v_inst_1168_, v_inst_1169_, v_inst_1170_, v_mod_1171_, v_isMeta_boxed_1174_, v_hint_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_mod_1183_, uint8_t v_isMeta_1184_, lean_object* v_hint_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1177_, v_inst_1178_, v_inst_1179_, v_inst_1180_, v_inst_1181_, v_inst_1182_, v_mod_1183_, v_isMeta_1184_, v_hint_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_mod_1194_, lean_object* v_isMeta_1195_, lean_object* v_hint_1196_){
_start:
{
uint8_t v_isMeta_boxed_1197_; lean_object* v_res_1198_; 
v_isMeta_boxed_1197_ = lean_unbox(v_isMeta_1195_);
v_res_1198_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1187_, v_inst_1188_, v_inst_1189_, v_inst_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_mod_1194_, v_isMeta_boxed_1197_, v_hint_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, uint8_t v_isMeta_1206_, lean_object* v_toApplicative_1207_, lean_object* v_____do__lift_1208_){
_start:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = l_Lean_Environment_mainModule(v_____do__lift_1208_);
v___x_1210_ = lean_name_eq(v_modName_1199_, v___x_1209_);
lean_dec(v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_toApplicative_1207_);
v___x_1211_ = lean_box(0);
v___x_1212_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1200_, v_inst_1201_, v_inst_1202_, v_inst_1203_, v_inst_1204_, v_inst_1205_, v_modName_1199_, v_isMeta_1206_, v___x_1211_);
return v___x_1212_;
}
else
{
lean_object* v_toPure_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_inst_1205_);
lean_dec_ref(v_inst_1204_);
lean_dec(v_inst_1203_);
lean_dec_ref(v_inst_1202_);
lean_dec_ref(v_inst_1201_);
lean_dec_ref(v_inst_1200_);
lean_dec(v_modName_1199_);
v_toPure_1213_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_inc(v_toPure_1213_);
lean_dec_ref(v_toApplicative_1207_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_apply_2(v_toPure_1213_, lean_box(0), v___x_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_isMeta_1223_, lean_object* v_toApplicative_1224_, lean_object* v_____do__lift_1225_){
_start:
{
uint8_t v_isMeta_boxed_1226_; lean_object* v_res_1227_; 
v_isMeta_boxed_1226_ = lean_unbox(v_isMeta_1223_);
v_res_1227_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1216_, v_inst_1217_, v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_isMeta_boxed_1226_, v_toApplicative_1224_, v_____do__lift_1225_);
lean_dec_ref(v_____do__lift_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_modName_1234_, uint8_t v_isMeta_1235_){
_start:
{
lean_object* v_toApplicative_1236_; lean_object* v_toBind_1237_; lean_object* v_getEnv_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; 
v_toApplicative_1236_ = lean_ctor_get(v_inst_1228_, 0);
lean_inc_ref(v_toApplicative_1236_);
v_toBind_1237_ = lean_ctor_get(v_inst_1228_, 1);
lean_inc(v_toBind_1237_);
v_getEnv_1238_ = lean_ctor_get(v_inst_1229_, 0);
lean_inc(v_getEnv_1238_);
v___x_1239_ = lean_box(v_isMeta_1235_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1240_, 0, v_modName_1234_);
lean_closure_set(v___f_1240_, 1, v_inst_1228_);
lean_closure_set(v___f_1240_, 2, v_inst_1229_);
lean_closure_set(v___f_1240_, 3, v_inst_1230_);
lean_closure_set(v___f_1240_, 4, v_inst_1231_);
lean_closure_set(v___f_1240_, 5, v_inst_1232_);
lean_closure_set(v___f_1240_, 6, v_inst_1233_);
lean_closure_set(v___f_1240_, 7, v___x_1239_);
lean_closure_set(v___f_1240_, 8, v_toApplicative_1236_);
v___x_1241_ = lean_apply_4(v_toBind_1237_, lean_box(0), lean_box(0), v_getEnv_1238_, v___f_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_modName_1248_, lean_object* v_isMeta_1249_){
_start:
{
uint8_t v_isMeta_boxed_1250_; lean_object* v_res_1251_; 
v_isMeta_boxed_1250_ = lean_unbox(v_isMeta_1249_);
v_res_1251_ = l_Lean_recordExtraModUse___redArg(v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v_inst_1246_, v_inst_1247_, v_modName_1248_, v_isMeta_boxed_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_modName_1259_, uint8_t v_isMeta_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_recordExtraModUse___redArg(v_inst_1253_, v_inst_1254_, v_inst_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_modName_1259_, v_isMeta_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_modName_1269_, lean_object* v_isMeta_1270_){
_start:
{
uint8_t v_isMeta_boxed_1271_; lean_object* v_res_1272_; 
v_isMeta_boxed_1271_ = lean_unbox(v_isMeta_1270_);
v_res_1272_ = l_Lean_recordExtraModUse(v_m_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_inst_1268_, v_modName_1269_, v_isMeta_boxed_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1273_, lean_object* v_____s_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_apply_2(v_toPure_1273_, lean_box(0), v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1277_, lean_object* v_toPure_1278_, lean_object* v_r_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1277_);
v___x_1281_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1282_, lean_object* v___x_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_declName_1290_, lean_object* v_toBind_1291_, lean_object* v___f_1292_, lean_object* v_a_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v_modules_1297_; lean_object* v___x_1298_; lean_object* v_toImport_1299_; lean_object* v_module_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1296_ = l_Lean_Environment_header(v_env_1282_);
v_modules_1297_ = lean_ctor_get(v___x_1296_, 3);
lean_inc_ref(v_modules_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = lean_array_get(v___x_1283_, v_modules_1297_, v_a_1293_);
lean_dec_ref(v_modules_1297_);
v_toImport_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc_ref(v_toImport_1299_);
lean_dec(v___x_1298_);
v_module_1300_ = lean_ctor_get(v_toImport_1299_, 0);
lean_inc(v_module_1300_);
lean_dec_ref(v_toImport_1299_);
v___x_1301_ = 0;
v___x_1302_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1284_, v_inst_1285_, v_inst_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v_module_1300_, v___x_1301_, v_declName_1290_);
v___x_1303_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v___x_1302_, v___f_1292_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1304_, lean_object* v___x_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_declName_1312_, lean_object* v_toBind_1313_, lean_object* v___f_1314_, lean_object* v_a_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1304_, v___x_1305_, v_inst_1306_, v_inst_1307_, v_inst_1308_, v_inst_1309_, v_inst_1310_, v_inst_1311_, v_declName_1312_, v_toBind_1313_, v___f_1314_, v_a_1315_, v_x_1316_, v___y_1317_);
lean_dec(v_a_1315_);
lean_dec_ref(v_env_1304_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1319_, lean_object* v_env_1320_, lean_object* v___x_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_declName_1328_, lean_object* v_toBind_1329_, lean_object* v___f_1330_, lean_object* v___x_1331_, lean_object* v___x_1332_, lean_object* v___x_1333_, lean_object* v_____r_1334_){
_start:
{
lean_object* v___y_1336_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1344_ = l_Lean_indirectModUseExt;
v___x_1345_ = lean_box(1);
v___x_1346_ = lean_box(0);
lean_inc_ref(v_env_1320_);
v___x_1347_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1331_, v___x_1344_, v_env_1320_, v___x_1345_, v___x_1346_);
lean_inc(v_declName_1328_);
v___x_1348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1332_, v___x_1333_, v___x_1347_, v_declName_1328_);
lean_dec(v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1336_ = v___x_1349_;
goto v___jp_1335_;
}
else
{
lean_object* v_val_1350_; 
v_val_1350_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_val_1350_);
lean_dec_ref(v___x_1348_);
v___y_1336_ = v_val_1350_;
goto v___jp_1335_;
}
v___jp_1335_:
{
lean_object* v___x_1337_; lean_object* v___f_1338_; lean_object* v___f_1339_; size_t v_sz_1340_; size_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1337_ = lean_box(0);
v___f_1338_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1338_, 0, v___x_1337_);
lean_closure_set(v___f_1338_, 1, v_toPure_1319_);
lean_inc(v_toBind_1329_);
lean_inc_ref(v_inst_1322_);
v___f_1339_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1339_, 0, v_env_1320_);
lean_closure_set(v___f_1339_, 1, v___x_1321_);
lean_closure_set(v___f_1339_, 2, v_inst_1322_);
lean_closure_set(v___f_1339_, 3, v_inst_1323_);
lean_closure_set(v___f_1339_, 4, v_inst_1324_);
lean_closure_set(v___f_1339_, 5, v_inst_1325_);
lean_closure_set(v___f_1339_, 6, v_inst_1326_);
lean_closure_set(v___f_1339_, 7, v_inst_1327_);
lean_closure_set(v___f_1339_, 8, v_declName_1328_);
lean_closure_set(v___f_1339_, 9, v_toBind_1329_);
lean_closure_set(v___f_1339_, 10, v___f_1338_);
v_sz_1340_ = lean_array_size(v___y_1336_);
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1322_, v___y_1336_, v___f_1339_, v_sz_1340_, v___x_1341_, v___x_1337_);
v___x_1343_ = lean_apply_4(v_toBind_1329_, lean_box(0), lean_box(0), v___x_1342_, v___f_1330_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_declName_1358_, lean_object* v_toBind_1359_, lean_object* v___f_1360_, uint8_t v_isMeta_1361_, lean_object* v_____do__lift_1362_){
_start:
{
uint8_t v___y_1364_; 
if (v_isMeta_1361_ == 0)
{
lean_dec_ref(v_____do__lift_1362_);
v___y_1364_ = v_isMeta_1361_;
goto v___jp_1363_;
}
else
{
uint8_t v___x_1369_; 
lean_inc(v_declName_1358_);
v___x_1369_ = l_Lean_isMarkedMeta(v_____do__lift_1362_, v_declName_1358_);
if (v___x_1369_ == 0)
{
v___y_1364_ = v_isMeta_1361_;
goto v___jp_1363_;
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = 0;
v___y_1364_ = v___x_1370_;
goto v___jp_1363_;
}
}
v___jp_1363_:
{
lean_object* v_toImport_1365_; lean_object* v_module_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_toImport_1365_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_ref(v_toImport_1365_);
lean_dec_ref(v___x_1351_);
v_module_1366_ = lean_ctor_get(v_toImport_1365_, 0);
lean_inc(v_module_1366_);
lean_dec_ref(v_toImport_1365_);
v___x_1367_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1352_, v_inst_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_inst_1357_, v_module_1366_, v___y_1364_, v_declName_1358_);
v___x_1368_ = lean_apply_4(v_toBind_1359_, lean_box(0), lean_box(0), v___x_1367_, v___f_1360_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_declName_1378_, lean_object* v_toBind_1379_, lean_object* v___f_1380_, lean_object* v_isMeta_1381_, lean_object* v_____do__lift_1382_){
_start:
{
uint8_t v_isMeta_boxed_1383_; lean_object* v_res_1384_; 
v_isMeta_boxed_1383_ = lean_unbox(v_isMeta_1381_);
v_res_1384_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1371_, v_inst_1372_, v_inst_1373_, v_inst_1374_, v_inst_1375_, v_inst_1376_, v_inst_1377_, v_declName_1378_, v_toBind_1379_, v___f_1380_, v_isMeta_boxed_1383_, v_____do__lift_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1385_, lean_object* v_declName_1386_, lean_object* v___x_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_toBind_1394_, lean_object* v___f_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, uint8_t v_isMeta_1399_, lean_object* v_getEnv_1400_, lean_object* v_env_1401_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1401_, v_declName_1386_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_dec_ref(v_env_1401_);
lean_dec(v_getEnv_1400_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec(v___f_1395_);
lean_dec(v_toBind_1394_);
lean_dec(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
lean_dec(v_inst_1391_);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
lean_dec_ref(v___x_1387_);
lean_dec(v_declName_1386_);
goto v___jp_1402_;
}
else
{
lean_object* v_val_1406_; lean_object* v___x_1407_; lean_object* v_modules_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_val_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_val_1406_);
lean_dec_ref(v___x_1405_);
v___x_1407_ = l_Lean_Environment_header(v_env_1401_);
v_modules_1408_ = lean_ctor_get(v___x_1407_, 3);
lean_inc_ref(v_modules_1408_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = lean_array_get_size(v_modules_1408_);
v___x_1410_ = lean_nat_dec_lt(v_val_1406_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_dec_ref(v_modules_1408_);
lean_dec(v_val_1406_);
lean_dec_ref(v_env_1401_);
lean_dec(v_getEnv_1400_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec(v___f_1395_);
lean_dec(v_toBind_1394_);
lean_dec(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
lean_dec(v_inst_1391_);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
lean_dec_ref(v___x_1387_);
lean_dec(v_declName_1386_);
goto v___jp_1402_;
}
else
{
lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; 
lean_inc(v_toBind_1394_);
lean_inc(v_declName_1386_);
lean_inc(v_inst_1393_);
lean_inc_ref(v_inst_1392_);
lean_inc(v_inst_1391_);
lean_inc_ref(v_inst_1390_);
lean_inc_ref(v_inst_1389_);
lean_inc_ref(v_inst_1388_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1411_, 0, v_toPure_1385_);
lean_closure_set(v___f_1411_, 1, v_env_1401_);
lean_closure_set(v___f_1411_, 2, v___x_1387_);
lean_closure_set(v___f_1411_, 3, v_inst_1388_);
lean_closure_set(v___f_1411_, 4, v_inst_1389_);
lean_closure_set(v___f_1411_, 5, v_inst_1390_);
lean_closure_set(v___f_1411_, 6, v_inst_1391_);
lean_closure_set(v___f_1411_, 7, v_inst_1392_);
lean_closure_set(v___f_1411_, 8, v_inst_1393_);
lean_closure_set(v___f_1411_, 9, v_declName_1386_);
lean_closure_set(v___f_1411_, 10, v_toBind_1394_);
lean_closure_set(v___f_1411_, 11, v___f_1395_);
lean_closure_set(v___f_1411_, 12, v___x_1396_);
lean_closure_set(v___f_1411_, 13, v___x_1397_);
lean_closure_set(v___f_1411_, 14, v___x_1398_);
v___x_1412_ = lean_array_fget(v_modules_1408_, v_val_1406_);
lean_dec(v_val_1406_);
lean_dec_ref(v_modules_1408_);
v___x_1413_ = lean_box(v_isMeta_1399_);
lean_inc(v_toBind_1394_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1414_, 0, v___x_1412_);
lean_closure_set(v___f_1414_, 1, v_inst_1388_);
lean_closure_set(v___f_1414_, 2, v_inst_1389_);
lean_closure_set(v___f_1414_, 3, v_inst_1390_);
lean_closure_set(v___f_1414_, 4, v_inst_1391_);
lean_closure_set(v___f_1414_, 5, v_inst_1392_);
lean_closure_set(v___f_1414_, 6, v_inst_1393_);
lean_closure_set(v___f_1414_, 7, v_declName_1386_);
lean_closure_set(v___f_1414_, 8, v_toBind_1394_);
lean_closure_set(v___f_1414_, 9, v___f_1411_);
lean_closure_set(v___f_1414_, 10, v___x_1413_);
v___x_1415_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v_getEnv_1400_, v___f_1414_);
return v___x_1415_;
}
}
v___jp_1402_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_apply_2(v_toPure_1385_, lean_box(0), v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1416_ = _args[0];
lean_object* v_declName_1417_ = _args[1];
lean_object* v___x_1418_ = _args[2];
lean_object* v_inst_1419_ = _args[3];
lean_object* v_inst_1420_ = _args[4];
lean_object* v_inst_1421_ = _args[5];
lean_object* v_inst_1422_ = _args[6];
lean_object* v_inst_1423_ = _args[7];
lean_object* v_inst_1424_ = _args[8];
lean_object* v_toBind_1425_ = _args[9];
lean_object* v___f_1426_ = _args[10];
lean_object* v___x_1427_ = _args[11];
lean_object* v___x_1428_ = _args[12];
lean_object* v___x_1429_ = _args[13];
lean_object* v_isMeta_1430_ = _args[14];
lean_object* v_getEnv_1431_ = _args[15];
lean_object* v_env_1432_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1433_; lean_object* v_res_1434_; 
v_isMeta_boxed_1433_ = lean_unbox(v_isMeta_1430_);
v_res_1434_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1416_, v_declName_1417_, v___x_1418_, v_inst_1419_, v_inst_1420_, v_inst_1421_, v_inst_1422_, v_inst_1423_, v_inst_1424_, v_toBind_1425_, v___f_1426_, v___x_1427_, v___x_1428_, v___x_1429_, v_isMeta_boxed_1433_, v_getEnv_1431_, v_env_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_declName_1441_, uint8_t v_isMeta_1442_){
_start:
{
lean_object* v_toApplicative_1443_; lean_object* v_toBind_1444_; lean_object* v_getEnv_1445_; lean_object* v_toPure_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; 
v_toApplicative_1443_ = lean_ctor_get(v_inst_1435_, 0);
v_toBind_1444_ = lean_ctor_get(v_inst_1435_, 1);
lean_inc(v_toBind_1444_);
v_getEnv_1445_ = lean_ctor_get(v_inst_1436_, 0);
lean_inc(v_getEnv_1445_);
v_toPure_1446_ = lean_ctor_get(v_toApplicative_1443_, 1);
lean_inc(v_toPure_1446_);
v___x_1447_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1448_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1449_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1450_ = l_Lean_instInhabitedEffectiveImport_default;
lean_inc(v_toPure_1446_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1451_, 0, v_toPure_1446_);
v___x_1452_ = lean_box(v_isMeta_1442_);
lean_inc(v_getEnv_1445_);
lean_inc(v_toBind_1444_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1453_, 0, v_toPure_1446_);
lean_closure_set(v___f_1453_, 1, v_declName_1441_);
lean_closure_set(v___f_1453_, 2, v___x_1450_);
lean_closure_set(v___f_1453_, 3, v_inst_1435_);
lean_closure_set(v___f_1453_, 4, v_inst_1436_);
lean_closure_set(v___f_1453_, 5, v_inst_1437_);
lean_closure_set(v___f_1453_, 6, v_inst_1438_);
lean_closure_set(v___f_1453_, 7, v_inst_1439_);
lean_closure_set(v___f_1453_, 8, v_inst_1440_);
lean_closure_set(v___f_1453_, 9, v_toBind_1444_);
lean_closure_set(v___f_1453_, 10, v___f_1451_);
lean_closure_set(v___f_1453_, 11, v___x_1449_);
lean_closure_set(v___f_1453_, 12, v___x_1447_);
lean_closure_set(v___f_1453_, 13, v___x_1448_);
lean_closure_set(v___f_1453_, 14, v___x_1452_);
lean_closure_set(v___f_1453_, 15, v_getEnv_1445_);
v___x_1454_ = lean_apply_4(v_toBind_1444_, lean_box(0), lean_box(0), v_getEnv_1445_, v___f_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_declName_1461_, lean_object* v_isMeta_1462_){
_start:
{
uint8_t v_isMeta_boxed_1463_; lean_object* v_res_1464_; 
v_isMeta_boxed_1463_ = lean_unbox(v_isMeta_1462_);
v_res_1464_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1455_, v_inst_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_, v_inst_1460_, v_declName_1461_, v_isMeta_boxed_1463_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_declName_1472_, uint8_t v_isMeta_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1466_, v_inst_1467_, v_inst_1468_, v_inst_1469_, v_inst_1470_, v_inst_1471_, v_declName_1472_, v_isMeta_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_declName_1482_, lean_object* v_isMeta_1483_){
_start:
{
uint8_t v_isMeta_boxed_1484_; lean_object* v_res_1485_; 
v_isMeta_boxed_1484_ = lean_unbox(v_isMeta_1483_);
v_res_1485_ = l_Lean_recordExtraModUseFromDecl(v_m_1475_, v_inst_1476_, v_inst_1477_, v_inst_1478_, v_inst_1479_, v_inst_1480_, v_inst_1481_, v_declName_1482_, v_isMeta_boxed_1484_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1486_, lean_object* v_e_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_box(0);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_box(0);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1491_);
lean_dec_ref(v_x_1491_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_array_mk(v_es_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1511_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1513_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1517_, lean_object* v_modIdx_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1519_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1520_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1521_ = 0;
v___x_1522_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1519_, v___x_1520_, v_env_1517_, v_modIdx_1518_, v___x_1521_);
v___x_1523_ = lean_array_get_size(v___x_1522_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_nat_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = 1;
return v___x_1526_;
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = 0;
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1528_, lean_object* v_modIdx_1529_){
_start:
{
uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_res_1530_ = l_Lean_isExtraRevModUse(v_env_1528_, v_modIdx_1529_);
lean_dec(v_modIdx_1529_);
lean_dec_ref(v_env_1528_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v_toEnvExtension_1534_; lean_object* v_asyncMode_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_toEnvExtension_1534_ = lean_ctor_get(v___x_1532_, 0);
v_asyncMode_1535_ = lean_ctor_get(v_toEnvExtension_1534_, 2);
lean_inc(v_asyncMode_1535_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1532_, v_x_1533_, v___x_1536_, v_asyncMode_1535_, v___x_1537_);
lean_dec(v_asyncMode_1535_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v_modifyEnv_1542_, lean_object* v___f_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_cls_1548_, lean_object* v_toBind_1549_, lean_object* v___f_1550_, uint8_t v_____do__lift_1551_){
_start:
{
if (v_____do__lift_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec(v___f_1550_);
lean_dec(v_toBind_1549_);
lean_dec(v_cls_1548_);
lean_dec(v_inst_1547_);
lean_dec_ref(v_inst_1546_);
lean_dec_ref(v_inst_1545_);
lean_dec_ref(v_inst_1544_);
v___x_1552_ = lean_apply_1(v_modifyEnv_1542_, v___f_1543_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec_ref(v___f_1543_);
lean_dec(v_modifyEnv_1542_);
v___x_1553_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1);
v___x_1554_ = l_Lean_addTrace___redArg(v_inst_1544_, v_inst_1545_, v_inst_1546_, v_inst_1547_, v_cls_1548_, v___x_1553_);
v___x_1555_ = lean_apply_4(v_toBind_1549_, lean_box(0), lean_box(0), v___x_1554_, v___f_1550_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object* v_modifyEnv_1556_, lean_object* v___f_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_cls_1562_, lean_object* v_toBind_1563_, lean_object* v___f_1564_, lean_object* v_____do__lift_1565_){
_start:
{
uint8_t v_____do__lift_253__boxed_1566_; lean_object* v_res_1567_; 
v_____do__lift_253__boxed_1566_ = lean_unbox(v_____do__lift_1565_);
v_res_1567_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(v_modifyEnv_1556_, v___f_1557_, v_inst_1558_, v_inst_1559_, v_inst_1560_, v_inst_1561_, v_cls_1562_, v_toBind_1563_, v___f_1564_, v_____do__lift_253__boxed_1566_);
return v_res_1567_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___f_1569_; 
v___x_1568_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1569_, 0, v___x_1568_);
return v___f_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object* v___x_1570_, lean_object* v_toApplicative_1571_, lean_object* v_modifyEnv_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_toBind_1577_, lean_object* v_inst_1578_, lean_object* v_____do__lift_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1580_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1581_ = lean_box(1);
v___x_1582_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1570_, v___x_1580_, v_____do__lift_1579_, v___x_1581_);
v___x_1583_ = l_List_isEmpty___redArg(v___x_1582_);
lean_dec(v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v_toPure_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v_inst_1578_);
lean_dec(v_toBind_1577_);
lean_dec(v_inst_1576_);
lean_dec_ref(v_inst_1575_);
lean_dec_ref(v_inst_1574_);
lean_dec_ref(v_inst_1573_);
lean_dec(v_modifyEnv_1572_);
v_toPure_1584_ = lean_ctor_get(v_toApplicative_1571_, 1);
lean_inc(v_toPure_1584_);
lean_dec_ref(v_toApplicative_1571_);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_apply_2(v_toPure_1584_, lean_box(0), v___x_1585_);
return v___x_1586_;
}
else
{
lean_object* v___f_1587_; lean_object* v___f_1588_; lean_object* v_cls_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec_ref(v_toApplicative_1571_);
v___f_1587_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0);
lean_inc(v_modifyEnv_1572_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1588_, 0, v_modifyEnv_1572_);
lean_closure_set(v___f_1588_, 1, v___f_1587_);
v_cls_1589_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
lean_inc(v_toBind_1577_);
lean_inc_ref(v_inst_1574_);
lean_inc_ref(v_inst_1573_);
v___f_1590_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1590_, 0, v_modifyEnv_1572_);
lean_closure_set(v___f_1590_, 1, v___f_1587_);
lean_closure_set(v___f_1590_, 2, v_inst_1573_);
lean_closure_set(v___f_1590_, 3, v_inst_1574_);
lean_closure_set(v___f_1590_, 4, v_inst_1575_);
lean_closure_set(v___f_1590_, 5, v_inst_1576_);
lean_closure_set(v___f_1590_, 6, v_cls_1589_);
lean_closure_set(v___f_1590_, 7, v_toBind_1577_);
lean_closure_set(v___f_1590_, 8, v___f_1588_);
v___x_1591_ = l_Lean_isTracingEnabledFor___redArg(v_inst_1573_, v_inst_1574_, v_inst_1578_, v_cls_1589_);
v___x_1592_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v___x_1591_, v___f_1590_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_){
_start:
{
lean_object* v_toApplicative_1599_; lean_object* v_toBind_1600_; lean_object* v_getEnv_1601_; lean_object* v_modifyEnv_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; 
v_toApplicative_1599_ = lean_ctor_get(v_inst_1593_, 0);
lean_inc_ref(v_toApplicative_1599_);
v_toBind_1600_ = lean_ctor_get(v_inst_1593_, 1);
lean_inc(v_toBind_1600_);
v_getEnv_1601_ = lean_ctor_get(v_inst_1594_, 0);
lean_inc(v_getEnv_1601_);
v_modifyEnv_1602_ = lean_ctor_get(v_inst_1594_, 1);
lean_inc(v_modifyEnv_1602_);
lean_dec_ref(v_inst_1594_);
v___x_1603_ = lean_box(0);
lean_inc(v_toBind_1600_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1604_, 0, v___x_1603_);
lean_closure_set(v___f_1604_, 1, v_toApplicative_1599_);
lean_closure_set(v___f_1604_, 2, v_modifyEnv_1602_);
lean_closure_set(v___f_1604_, 3, v_inst_1593_);
lean_closure_set(v___f_1604_, 4, v_inst_1595_);
lean_closure_set(v___f_1604_, 5, v_inst_1597_);
lean_closure_set(v___f_1604_, 6, v_inst_1598_);
lean_closure_set(v___f_1604_, 7, v_toBind_1600_);
lean_closure_set(v___f_1604_, 8, v_inst_1596_);
v___x_1605_ = lean_apply_4(v_toBind_1600_, lean_box(0), lean_box(0), v_getEnv_1601_, v___f_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1607_, v_inst_1608_, v_inst_1609_, v_inst_1610_, v_inst_1611_, v_inst_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(4259277863u);
v___x_1646_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1647_ = l_Lean_Name_num___override(v___x_1646_, v___x_1645_);
return v___x_1647_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1650_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1651_ = l_Lean_Name_str___override(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1654_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1655_ = l_Lean_Name_str___override(v___x_1654_, v___x_1653_);
return v___x_1655_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_unsigned_to_nat(2u);
v___x_1657_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1658_ = l_Lean_Name_num___override(v___x_1657_, v___x_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
v___x_1661_ = 0;
v___x_1662_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1663_ = l_Lean_registerTraceClass(v___x_1660_, v___x_1661_, v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1665_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_indirectModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_indirectModUseExt);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ExtraModUses_447004708____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_extraModUses = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_extraModUses);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ExtraModUses(builtin);
}
#ifdef __cplusplus
}
#endif
