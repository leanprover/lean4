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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_mk(lean_object*);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
static lean_once_cell_t l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 226, 202, 112, 104, 166, 144, 212)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v_size_131_; lean_object* v_buckets_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_179_; 
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
v___x_129_ = lean_array_uset(v___y_127_, v___y_125_, v___y_126_);
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
v___y_125_ = v___x_149_;
v___y_126_ = v_bkt_x27_173_;
v___y_127_ = v_buckets_x27_172_;
v___y_128_ = v___x_176_;
goto v___jp_124_;
}
else
{
v___y_125_ = v___x_149_;
v___y_126_ = v_bkt_x27_173_;
v___y_127_ = v_buckets_x27_172_;
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
uint8_t v_____do__lift_577__boxed_381_; lean_object* v_res_382_; 
v_____do__lift_577__boxed_381_ = lean_unbox(v_____do__lift_380_);
v_res_382_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_modifyEnv_369_, v___f_370_, v_declName_371_, v_kind_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_cls_377_, v_toBind_378_, v___f_379_, v_____do__lift_577__boxed_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v_toPure_386_, lean_object* v_cls_387_, lean_object* v_____do__lift_388_, lean_object* v_____do__lift_389_){
_start:
{
uint8_t v_hasTrace_390_; 
v_hasTrace_390_ = lean_ctor_get_uint8(v_____do__lift_389_, sizeof(void*)*1);
if (v_hasTrace_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_cls_387_);
v___x_391_ = lean_box(v_hasTrace_390_);
v___x_392_ = lean_apply_2(v_toPure_386_, lean_box(0), v___x_391_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
v___x_394_ = l_Lean_Name_append(v___x_393_, v_cls_387_);
v___x_395_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_388_, v_____do__lift_389_, v___x_394_);
lean_dec(v___x_394_);
v___x_396_ = lean_box(v___x_395_);
v___x_397_ = lean_apply_2(v_toPure_386_, lean_box(0), v___x_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___boxed(lean_object* v_toPure_398_, lean_object* v_cls_399_, lean_object* v_____do__lift_400_, lean_object* v_____do__lift_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_recordIndirectModUse___redArg___lam__3(v_toPure_398_, v_cls_399_, v_____do__lift_400_, v_____do__lift_401_);
lean_dec_ref(v_____do__lift_401_);
lean_dec_ref(v_____do__lift_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object* v_toPure_403_, lean_object* v_cls_404_, lean_object* v_toBind_405_, lean_object* v_inst_406_, lean_object* v_____do__lift_407_){
_start:
{
lean_object* v___f_408_; lean_object* v___x_409_; 
v___f_408_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_408_, 0, v_toPure_403_);
lean_closure_set(v___f_408_, 1, v_cls_404_);
lean_closure_set(v___f_408_, 2, v_____do__lift_407_);
v___x_409_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v_inst_406_, v___f_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v___x_413_, lean_object* v_kind_414_, lean_object* v_declName_415_, lean_object* v___x_416_, lean_object* v_inst_417_, lean_object* v_toApplicative_418_, lean_object* v_modifyEnv_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_toBind_423_, lean_object* v_inst_424_, lean_object* v_____do__lift_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_426_ = l_Lean_indirectModUseExt;
v___x_427_ = lean_box(2);
v___x_428_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_413_, v___x_426_, v_____do__lift_425_, v___x_427_);
lean_inc(v_declName_415_);
lean_inc_ref(v_kind_414_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_kind_414_);
lean_ctor_set(v___x_429_, 1, v_declName_415_);
lean_inc_ref(v___x_429_);
v___x_430_ = l_List_elem___redArg(v___x_416_, v___x_429_, v___x_428_);
if (v___x_430_ == 0)
{
lean_object* v_getInheritedTraceOptions_431_; lean_object* v_toPure_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v_cls_435_; lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_getInheritedTraceOptions_431_ = lean_ctor_get(v_inst_417_, 2);
lean_inc(v_getInheritedTraceOptions_431_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_toPure_432_);
lean_dec_ref(v_toApplicative_418_);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_433_, 0, v___x_426_);
lean_closure_set(v___f_433_, 1, v___x_429_);
lean_inc_ref(v___f_433_);
lean_inc(v_modifyEnv_419_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_434_, 0, v_modifyEnv_419_);
lean_closure_set(v___f_434_, 1, v___f_433_);
v_cls_435_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_423_, 3);
v___f_436_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_436_, 0, v_modifyEnv_419_);
lean_closure_set(v___f_436_, 1, v___f_433_);
lean_closure_set(v___f_436_, 2, v_declName_415_);
lean_closure_set(v___f_436_, 3, v_kind_414_);
lean_closure_set(v___f_436_, 4, v_inst_420_);
lean_closure_set(v___f_436_, 5, v_inst_417_);
lean_closure_set(v___f_436_, 6, v_inst_421_);
lean_closure_set(v___f_436_, 7, v_inst_422_);
lean_closure_set(v___f_436_, 8, v_cls_435_);
lean_closure_set(v___f_436_, 9, v_toBind_423_);
lean_closure_set(v___f_436_, 10, v___f_434_);
v___f_437_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_437_, 0, v_toPure_432_);
lean_closure_set(v___f_437_, 1, v_cls_435_);
lean_closure_set(v___f_437_, 2, v_toBind_423_);
lean_closure_set(v___f_437_, 3, v_inst_424_);
v___x_438_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_431_, v___f_437_);
v___x_439_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v___x_438_, v___f_436_);
return v___x_439_;
}
else
{
lean_object* v_toPure_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v___x_429_);
lean_dec(v_inst_424_);
lean_dec(v_toBind_423_);
lean_dec(v_inst_422_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
lean_dec(v_modifyEnv_419_);
lean_dec_ref(v_inst_417_);
lean_dec(v_declName_415_);
lean_dec_ref(v_kind_414_);
v_toPure_440_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_toPure_440_);
lean_dec_ref(v_toApplicative_418_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_apply_2(v_toPure_440_, lean_box(0), v___x_441_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_kind_449_, lean_object* v_declName_450_){
_start:
{
lean_object* v_toApplicative_451_; lean_object* v_toBind_452_; lean_object* v_getEnv_453_; lean_object* v_modifyEnv_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_toApplicative_451_ = lean_ctor_get(v_inst_443_, 0);
lean_inc_ref(v_toApplicative_451_);
v_toBind_452_ = lean_ctor_get(v_inst_443_, 1);
lean_inc_n(v_toBind_452_, 2);
v_getEnv_453_ = lean_ctor_get(v_inst_444_, 0);
lean_inc(v_getEnv_453_);
v_modifyEnv_454_ = lean_ctor_get(v_inst_444_, 1);
lean_inc(v_modifyEnv_454_);
lean_dec_ref(v_inst_444_);
v___x_455_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_456_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5), 13, 12);
lean_closure_set(v___f_457_, 0, v___x_456_);
lean_closure_set(v___f_457_, 1, v_kind_449_);
lean_closure_set(v___f_457_, 2, v_declName_450_);
lean_closure_set(v___f_457_, 3, v___x_455_);
lean_closure_set(v___f_457_, 4, v_inst_445_);
lean_closure_set(v___f_457_, 5, v_toApplicative_451_);
lean_closure_set(v___f_457_, 6, v_modifyEnv_454_);
lean_closure_set(v___f_457_, 7, v_inst_443_);
lean_closure_set(v___f_457_, 8, v_inst_447_);
lean_closure_set(v___f_457_, 9, v_inst_448_);
lean_closure_set(v___f_457_, 10, v_toBind_452_);
lean_closure_set(v___f_457_, 11, v_inst_446_);
v___x_458_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v_getEnv_453_, v___f_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_kind_466_, lean_object* v_declName_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_recordIndirectModUse___redArg(v_inst_460_, v_inst_461_, v_inst_462_, v_inst_463_, v_inst_464_, v_inst_465_, v_kind_466_, v_declName_467_);
return v___x_468_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_module_471_; uint8_t v_isExported_472_; uint8_t v_isMeta_473_; lean_object* v_module_474_; uint8_t v_isExported_475_; uint8_t v_isMeta_476_; uint8_t v___y_478_; uint8_t v___x_479_; 
v_module_471_ = lean_ctor_get(v_x_469_, 0);
v_isExported_472_ = lean_ctor_get_uint8(v_x_469_, sizeof(void*)*1);
v_isMeta_473_ = lean_ctor_get_uint8(v_x_469_, sizeof(void*)*1 + 1);
v_module_474_ = lean_ctor_get(v_x_470_, 0);
v_isExported_475_ = lean_ctor_get_uint8(v_x_470_, sizeof(void*)*1);
v_isMeta_476_ = lean_ctor_get_uint8(v_x_470_, sizeof(void*)*1 + 1);
v___x_479_ = lean_name_eq(v_module_471_, v_module_474_);
if (v___x_479_ == 0)
{
return v___x_479_;
}
else
{
if (v_isExported_472_ == 0)
{
if (v_isExported_475_ == 0)
{
v___y_478_ = v___x_479_;
goto v___jp_477_;
}
else
{
return v_isExported_472_;
}
}
else
{
v___y_478_ = v_isExported_475_;
goto v___jp_477_;
}
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
return v___y_478_;
}
else
{
if (v_isMeta_473_ == 0)
{
if (v_isMeta_476_ == 0)
{
return v___y_478_;
}
else
{
return v_isMeta_473_;
}
}
else
{
return v_isMeta_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Lean_instBEqExtraModUse_beq(v_x_480_, v_x_481_);
lean_dec_ref(v_x_481_);
lean_dec_ref(v_x_480_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_486_){
_start:
{
lean_object* v_module_487_; uint8_t v_isExported_488_; uint8_t v_isMeta_489_; uint64_t v___y_491_; uint64_t v___y_492_; uint64_t v___x_498_; uint64_t v___y_500_; 
v_module_487_ = lean_ctor_get(v_x_486_, 0);
v_isExported_488_ = lean_ctor_get_uint8(v_x_486_, sizeof(void*)*1);
v_isMeta_489_ = lean_ctor_get_uint8(v_x_486_, sizeof(void*)*1 + 1);
v___x_498_ = 0ULL;
if (lean_obj_tag(v_module_487_) == 0)
{
uint64_t v___x_504_; 
v___x_504_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_500_ = v___x_504_;
goto v___jp_499_;
}
else
{
uint64_t v_hash_505_; 
v_hash_505_ = lean_ctor_get_uint64(v_module_487_, sizeof(void*)*2);
v___y_500_ = v_hash_505_;
goto v___jp_499_;
}
v___jp_490_:
{
uint64_t v___x_493_; 
v___x_493_ = lean_uint64_mix_hash(v___y_491_, v___y_492_);
if (v_isMeta_489_ == 0)
{
uint64_t v___x_494_; uint64_t v___x_495_; 
v___x_494_ = 13ULL;
v___x_495_ = lean_uint64_mix_hash(v___x_493_, v___x_494_);
return v___x_495_;
}
else
{
uint64_t v___x_496_; uint64_t v___x_497_; 
v___x_496_ = 11ULL;
v___x_497_ = lean_uint64_mix_hash(v___x_493_, v___x_496_);
return v___x_497_;
}
}
v___jp_499_:
{
uint64_t v___x_501_; 
v___x_501_ = lean_uint64_mix_hash(v___x_498_, v___y_500_);
if (v_isExported_488_ == 0)
{
uint64_t v___x_502_; 
v___x_502_ = 13ULL;
v___y_491_ = v___x_501_;
v___y_492_ = v___x_502_;
goto v___jp_490_;
}
else
{
uint64_t v___x_503_; 
v___x_503_ = 11ULL;
v___y_491_ = v___x_501_;
v___y_492_ = v___x_503_;
goto v___jp_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_506_){
_start:
{
uint64_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Lean_instHashableExtraModUse_hash(v_x_506_);
lean_dec_ref(v_x_506_);
v_r_508_ = lean_box_uint64(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_nat_to_int(v_a_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(10u);
v___x_527_ = lean_nat_to_int(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(14u);
v___x_535_ = lean_nat_to_int(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_541_ = lean_string_length(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_543_ = lean_nat_to_int(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_548_){
_start:
{
lean_object* v_module_549_; uint8_t v_isExported_550_; uint8_t v_isMeta_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_module_549_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_module_549_);
v_isExported_550_ = lean_ctor_get_uint8(v_x_548_, sizeof(void*)*1);
v_isMeta_551_ = lean_ctor_get_uint8(v_x_548_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_548_);
v___x_552_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_553_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_554_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Lean_Name_reprPrec(v_module_549_, v___x_555_);
v___x_557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_554_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = 0;
v___x_559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*1, v___x_558_);
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_553_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = lean_box(1);
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_552_);
v___x_568_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_569_ = l_Bool_repr___redArg(v_isExported_550_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*1, v___x_558_);
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_567_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_561_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_563_);
v___x_575_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_552_);
v___x_578_ = l_Bool_repr___redArg(v_isMeta_551_);
v___x_579_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_554_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_558_);
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_577_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_583_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_581_);
v___x_585_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_582_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*1, v___x_558_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_589_, lean_object* v_prec_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_592_, lean_object* v_prec_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_instReprExtraModUse_repr(v_x_592_, v_prec_593_);
lean_dec(v_prec_593_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_597_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_entries_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_608_ = lean_array_mk(v_entries_606_);
v___x_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_entries_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_610_, v_x_611_, v_entries_612_);
lean_dec_ref(v_x_611_);
lean_dec_ref(v_x_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_mk(v_es_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_empty___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_box(0));
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, &l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_619_);
lean_dec_ref(v_x_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_ks_625_; lean_object* v_vs_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_650_; 
v_ks_625_ = lean_ctor_get(v_x_621_, 0);
v_vs_626_ = lean_ctor_get(v_x_621_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_650_ == 0)
{
v___x_628_ = v_x_621_;
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_vs_626_);
lean_inc(v_ks_625_);
lean_dec(v_x_621_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_array_get_size(v_ks_625_);
v___x_631_ = lean_nat_dec_lt(v_x_622_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec(v_x_622_);
v___x_632_ = lean_array_push(v_ks_625_, v_x_623_);
v___x_633_ = lean_array_push(v_vs_626_, v_x_624_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_633_);
lean_ctor_set(v___x_628_, 0, v___x_632_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
else
{
lean_object* v_k_x27_637_; uint8_t v___x_638_; 
v_k_x27_637_ = lean_array_fget_borrowed(v_ks_625_, v_x_622_);
v___x_638_ = l_Lean_instBEqExtraModUse_beq(v_x_623_, v_k_x27_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_640_; 
if (v_isShared_629_ == 0)
{
v___x_640_ = v___x_628_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_ks_625_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_vs_626_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_x_622_, v___x_641_);
lean_dec(v_x_622_);
v_x_621_ = v___x_640_;
v_x_622_ = v___x_642_;
goto _start;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = lean_array_fset(v_ks_625_, v_x_622_, v_x_623_);
v___x_646_ = lean_array_fset(v_vs_626_, v_x_622_, v_x_624_);
lean_dec(v_x_622_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_646_);
lean_ctor_set(v___x_628_, 0, v___x_645_);
v___x_648_ = v___x_628_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_651_, lean_object* v_k_652_, lean_object* v_v_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_651_, v___x_654_, v_k_652_, v_v_653_);
return v___x_655_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; 
v___x_656_ = ((size_t)5ULL);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_shift_left(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_659_; size_t v___x_660_; size_t v___x_661_; 
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_661_ = lean_usize_sub(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_663_, size_t v_x_664_, size_t v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v_es_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v_j_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_es_668_ = lean_ctor_get(v_x_663_, 0);
v___x_669_ = ((size_t)5ULL);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1);
v___x_672_ = lean_usize_land(v_x_664_, v___x_671_);
v_j_673_ = lean_usize_to_nat(v___x_672_);
v___x_674_ = lean_array_get_size(v_es_668_);
v___x_675_ = lean_nat_dec_lt(v_j_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec(v_j_673_);
lean_dec(v_x_667_);
lean_dec_ref(v_x_666_);
return v_x_663_;
}
else
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_712_; 
lean_inc_ref(v_es_668_);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v_x_663_, 0);
lean_dec(v_unused_713_);
v___x_677_ = v_x_663_;
v_isShared_678_ = v_isSharedCheck_712_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_x_663_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_712_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_v_679_; lean_object* v___x_680_; lean_object* v_xs_x27_681_; lean_object* v___y_683_; 
v_v_679_ = lean_array_fget(v_es_668_, v_j_673_);
v___x_680_ = lean_box(0);
v_xs_x27_681_ = lean_array_fset(v_es_668_, v_j_673_, v___x_680_);
switch(lean_obj_tag(v_v_679_))
{
case 0:
{
lean_object* v_key_688_; lean_object* v_val_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v_key_688_ = lean_ctor_get(v_v_679_, 0);
v_val_689_ = lean_ctor_get(v_v_679_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_v_679_);
if (v_isSharedCheck_699_ == 0)
{
v___x_691_ = v_v_679_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_val_689_);
lean_inc(v_key_688_);
lean_dec(v_v_679_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_instBEqExtraModUse_beq(v_x_666_, v_key_688_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_del_object(v___x_691_);
v___x_694_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_688_, v_val_689_, v_x_666_, v_x_667_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
v___y_683_ = v___x_695_;
goto v___jp_682_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_val_689_);
lean_dec(v_key_688_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_x_667_);
lean_ctor_set(v___x_691_, 0, v_x_666_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_x_666_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_x_667_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v___y_683_ = v___x_697_;
goto v___jp_682_;
}
}
}
}
case 1:
{
lean_object* v_node_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
v_node_700_ = lean_ctor_get(v_v_679_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_v_679_);
if (v_isSharedCheck_710_ == 0)
{
v___x_702_ = v_v_679_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_node_700_);
lean_dec(v_v_679_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_704_ = lean_usize_shift_right(v_x_664_, v___x_669_);
v___x_705_ = lean_usize_add(v_x_665_, v___x_670_);
v___x_706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_700_, v___x_704_, v___x_705_, v_x_666_, v_x_667_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_706_);
v___x_708_ = v___x_702_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v___y_683_ = v___x_708_;
goto v___jp_682_;
}
}
}
default: 
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_x_666_);
lean_ctor_set(v___x_711_, 1, v_x_667_);
v___y_683_ = v___x_711_;
goto v___jp_682_;
}
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_array_fset(v_xs_x27_681_, v_j_673_, v___y_683_);
lean_dec(v_j_673_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_684_);
v___x_686_ = v___x_677_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_object* v_ks_714_; lean_object* v_vs_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_735_; 
v_ks_714_ = lean_ctor_get(v_x_663_, 0);
v_vs_715_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_735_ == 0)
{
v___x_717_ = v_x_663_;
v_isShared_718_ = v_isSharedCheck_735_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_vs_715_);
lean_inc(v_ks_714_);
lean_dec(v_x_663_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_735_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_ks_714_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_vs_715_);
v___x_720_ = v_reuseFailAlloc_734_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v_newNode_721_; uint8_t v___y_723_; size_t v___x_729_; uint8_t v___x_730_; 
v_newNode_721_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_720_, v_x_666_, v_x_667_);
v___x_729_ = ((size_t)7ULL);
v___x_730_ = lean_usize_dec_le(v___x_729_, v_x_665_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_721_);
v___x_732_ = lean_unsigned_to_nat(4u);
v___x_733_ = lean_nat_dec_lt(v___x_731_, v___x_732_);
lean_dec(v___x_731_);
v___y_723_ = v___x_733_;
goto v___jp_722_;
}
else
{
v___y_723_ = v___x_730_;
goto v___jp_722_;
}
v___jp_722_:
{
if (v___y_723_ == 0)
{
lean_object* v_ks_724_; lean_object* v_vs_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_ks_724_ = lean_ctor_get(v_newNode_721_, 0);
lean_inc_ref(v_ks_724_);
v_vs_725_ = lean_ctor_get(v_newNode_721_, 1);
lean_inc_ref(v_vs_725_);
lean_dec_ref(v_newNode_721_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2);
v___x_728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_665_, v_ks_724_, v_vs_725_, v___x_726_, v___x_727_);
lean_dec_ref(v_vs_725_);
lean_dec_ref(v_ks_724_);
return v___x_728_;
}
else
{
return v_newNode_721_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_736_, lean_object* v_keys_737_, lean_object* v_vals_738_, lean_object* v_i_739_, lean_object* v_entries_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_keys_737_);
v___x_742_ = lean_nat_dec_lt(v_i_739_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v_i_739_);
return v_entries_740_;
}
else
{
lean_object* v_k_743_; lean_object* v_v_744_; uint64_t v___x_745_; size_t v_h_746_; size_t v___x_747_; lean_object* v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; size_t v_h_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_k_743_ = lean_array_fget_borrowed(v_keys_737_, v_i_739_);
v_v_744_ = lean_array_fget_borrowed(v_vals_738_, v_i_739_);
v___x_745_ = l_Lean_instHashableExtraModUse_hash(v_k_743_);
v_h_746_ = lean_uint64_to_usize(v___x_745_);
v___x_747_ = ((size_t)5ULL);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_sub(v_depth_736_, v___x_749_);
v___x_751_ = lean_usize_mul(v___x_747_, v___x_750_);
v_h_752_ = lean_usize_shift_right(v_h_746_, v___x_751_);
v___x_753_ = lean_nat_add(v_i_739_, v___x_748_);
lean_dec(v_i_739_);
lean_inc(v_v_744_);
lean_inc(v_k_743_);
v___x_754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_740_, v_h_752_, v_depth_736_, v_k_743_, v_v_744_);
v_i_739_ = v___x_753_;
v_entries_740_ = v___x_754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_756_, lean_object* v_keys_757_, lean_object* v_vals_758_, lean_object* v_i_759_, lean_object* v_entries_760_){
_start:
{
size_t v_depth_boxed_761_; lean_object* v_res_762_; 
v_depth_boxed_761_ = lean_unbox_usize(v_depth_756_);
lean_dec(v_depth_756_);
v_res_762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_761_, v_keys_757_, v_vals_758_, v_i_759_, v_entries_760_);
lean_dec_ref(v_vals_758_);
lean_dec_ref(v_keys_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
size_t v_x_566__boxed_768_; size_t v_x_567__boxed_769_; lean_object* v_res_770_; 
v_x_566__boxed_768_ = lean_unbox_usize(v_x_764_);
lean_dec(v_x_764_);
v_x_567__boxed_769_ = lean_unbox_usize(v_x_765_);
lean_dec(v_x_765_);
v_res_770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_763_, v_x_566__boxed_768_, v_x_567__boxed_769_, v_x_766_, v_x_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
uint64_t v___x_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_774_ = l_Lean_instHashableExtraModUse_hash(v_x_772_);
v___x_775_ = lean_uint64_to_usize(v___x_774_);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_771_, v___x_775_, v___x_776_, v_x_772_, v_x_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_778_, lean_object* v_k_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_778_, v_k_779_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_array_get_size(v_keys_782_);
v___x_786_ = lean_nat_dec_lt(v_i_783_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec(v_i_783_);
return v___x_786_;
}
else
{
lean_object* v_k_x27_787_; uint8_t v___x_788_; 
v_k_x27_787_ = lean_array_fget_borrowed(v_keys_782_, v_i_783_);
v___x_788_ = l_Lean_instBEqExtraModUse_beq(v_k_784_, v_k_x27_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_i_783_, v___x_789_);
lean_dec(v_i_783_);
v_i_783_ = v___x_790_;
goto _start;
}
else
{
lean_dec(v_i_783_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_792_, lean_object* v_i_793_, lean_object* v_k_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_792_, v_i_793_, v_k_794_);
lean_dec_ref(v_k_794_);
lean_dec_ref(v_keys_792_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_797_, size_t v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_es_800_; lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v_j_805_; lean_object* v___x_806_; 
v_es_800_ = lean_ctor_get(v_x_797_, 0);
v___x_801_ = lean_box(2);
v___x_802_ = ((size_t)5ULL);
v___x_803_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1);
v___x_804_ = lean_usize_land(v_x_798_, v___x_803_);
v_j_805_ = lean_usize_to_nat(v___x_804_);
v___x_806_ = lean_array_get_borrowed(v___x_801_, v_es_800_, v_j_805_);
lean_dec(v_j_805_);
switch(lean_obj_tag(v___x_806_))
{
case 0:
{
lean_object* v_key_807_; uint8_t v___x_808_; 
v_key_807_ = lean_ctor_get(v___x_806_, 0);
v___x_808_ = l_Lean_instBEqExtraModUse_beq(v_x_799_, v_key_807_);
return v___x_808_;
}
case 1:
{
lean_object* v_node_809_; size_t v___x_810_; 
v_node_809_ = lean_ctor_get(v___x_806_, 0);
v___x_810_ = lean_usize_shift_right(v_x_798_, v___x_802_);
v_x_797_ = v_node_809_;
v_x_798_ = v___x_810_;
goto _start;
}
default: 
{
uint8_t v___x_812_; 
v___x_812_ = 0;
return v___x_812_;
}
}
}
else
{
lean_object* v_ks_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_ks_813_ = lean_ctor_get(v_x_797_, 0);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_813_, v___x_814_, v_x_799_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
size_t v_x_764__boxed_819_; uint8_t v_res_820_; lean_object* v_r_821_; 
v_x_764__boxed_819_ = lean_unbox_usize(v_x_817_);
lean_dec(v_x_817_);
v_res_820_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_816_, v_x_764__boxed_819_, v_x_818_);
lean_dec_ref(v_x_818_);
lean_dec_ref(v_x_816_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
uint64_t v___x_824_; size_t v___x_825_; uint8_t v___x_826_; 
v___x_824_ = l_Lean_instHashableExtraModUse_hash(v_x_823_);
v___x_825_ = lean_uint64_to_usize(v___x_824_);
v___x_826_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_822_, v___x_825_, v_x_823_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_827_, v_x_828_);
lean_dec_ref(v_x_828_);
lean_dec_ref(v_x_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_856_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_858_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_863_, v_x_864_, v_x_865_);
lean_dec_ref(v_x_865_);
lean_dec_ref(v_x_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, size_t v_x_875_, lean_object* v_x_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_874_, v_x_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
size_t v_x_913__boxed_882_; uint8_t v_res_883_; lean_object* v_r_884_; 
v_x_913__boxed_882_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_res_883_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_878_, v_x_879_, v_x_913__boxed_882_, v_x_881_);
lean_dec_ref(v_x_881_);
lean_dec_ref(v_x_879_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, size_t v_x_887_, size_t v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_886_, v_x_887_, v_x_888_, v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
size_t v_x_924__boxed_898_; size_t v_x_925__boxed_899_; lean_object* v_res_900_; 
v_x_924__boxed_898_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_x_925__boxed_899_ = lean_unbox_usize(v_x_895_);
lean_dec(v_x_895_);
v_res_900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_892_, v_x_893_, v_x_924__boxed_898_, v_x_925__boxed_899_, v_x_896_, v_x_897_);
return v_res_900_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_heq_904_, lean_object* v_i_905_, lean_object* v_k_906_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_902_, v_i_905_, v_k_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_908_, lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_heq_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_908_, v_keys_909_, v_vals_910_, v_heq_911_, v_i_912_, v_k_913_);
lean_dec_ref(v_k_913_);
lean_dec_ref(v_vals_910_);
lean_dec_ref(v_keys_909_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_916_, lean_object* v_n_917_, lean_object* v_k_918_, lean_object* v_v_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_917_, v_k_918_, v_v_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_921_, size_t v_depth_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_heq_925_, lean_object* v_i_926_, lean_object* v_entries_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_922_, v_keys_923_, v_vals_924_, v_i_926_, v_entries_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_929_, lean_object* v_depth_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_entries_935_){
_start:
{
size_t v_depth_boxed_936_; lean_object* v_res_937_; 
v_depth_boxed_936_ = lean_unbox_usize(v_depth_930_);
lean_dec(v_depth_930_);
v_res_937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_929_, v_depth_boxed_936_, v_keys_931_, v_vals_932_, v_heq_933_, v_i_934_, v_entries_935_);
lean_dec_ref(v_vals_932_);
lean_dec_ref(v_keys_931_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_939_, v_x_940_, v_x_941_, v_x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_945_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_946_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_950_, lean_object* v_modIdx_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; 
v___x_952_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_953_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_954_ = 0;
v___x_955_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_952_, v___x_953_, v_env_950_, v_modIdx_951_, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_956_, lean_object* v_modIdx_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_getExtraModUses(v_env_956_, v_modIdx_957_);
lean_dec(v_modIdx_957_);
lean_dec_ref(v_env_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_959_, lean_object* v_b_960_){
_start:
{
if (lean_obj_tag(v_as_x27_959_) == 0)
{
return v_b_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_head_961_ = lean_ctor_get(v_as_x27_959_, 0);
lean_inc(v_head_961_);
v_tail_962_ = lean_ctor_get(v_as_x27_959_, 1);
lean_inc(v_tail_962_);
lean_dec_ref(v_as_x27_959_);
v___x_963_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_964_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_965_ = lean_box(1);
v___x_966_ = lean_box(0);
lean_inc_ref(v_b_960_);
v___x_967_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_963_, v___x_964_, v_b_960_, v___x_965_, v___x_966_);
v___x_968_ = l_Lean_PersistentHashMap_contains___at___00Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_967_, v_head_961_);
lean_dec(v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v_toEnvExtension_969_; lean_object* v_asyncMode_970_; lean_object* v___x_971_; 
v_toEnvExtension_969_ = lean_ctor_get(v___x_964_, 0);
v_asyncMode_970_ = lean_ctor_get(v_toEnvExtension_969_, 2);
v___x_971_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_964_, v_b_960_, v_head_961_, v_asyncMode_970_, v___x_966_);
v_as_x27_959_ = v_tail_962_;
v_b_960_ = v___x_971_;
goto _start;
}
else
{
lean_dec(v_head_961_);
v_as_x27_959_ = v_tail_962_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_974_, lean_object* v_dest_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_976_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_977_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_978_ = lean_box(1);
v___x_979_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_976_, v___x_977_, v_src_974_, v___x_978_);
v___x_980_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_979_, v_dest_975_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_981_, lean_object* v_as_x27_982_, lean_object* v_b_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_982_, v_b_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_986_, lean_object* v_as_x27_987_, lean_object* v_b_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_986_, v_as_x27_987_, v_b_988_, v_a_989_);
lean_dec(v_as_986_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_991_, lean_object* v_entry_992_, lean_object* v___x_993_, lean_object* v_x_994_){
_start:
{
lean_object* v_toEnvExtension_995_; lean_object* v_asyncMode_996_; lean_object* v___x_997_; 
v_toEnvExtension_995_ = lean_ctor_get(v___x_991_, 0);
v_asyncMode_996_ = lean_ctor_get(v_toEnvExtension_995_, 2);
lean_inc(v_asyncMode_996_);
v___x_997_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_991_, v_x_994_, v_entry_992_, v_asyncMode_996_, v___x_993_);
lean_dec(v_asyncMode_996_);
return v___x_997_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4));
v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_modifyEnv_1017_, lean_object* v___f_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_cls_1023_, lean_object* v_toBind_1024_, lean_object* v___f_1025_, lean_object* v_mod_1026_, lean_object* v_hint_1027_, uint8_t v_isMeta_1028_, uint8_t v_isExporting_1029_, uint8_t v_____do__lift_1030_){
_start:
{
lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1038_; lean_object* v___y_1039_; 
if (v_____do__lift_1030_ == 0)
{
lean_object* v___x_1051_; 
lean_dec(v_hint_1027_);
lean_dec(v_mod_1026_);
lean_dec(v___f_1025_);
lean_dec(v_toBind_1024_);
lean_dec(v_cls_1023_);
lean_dec(v_inst_1022_);
lean_dec_ref(v_inst_1021_);
lean_dec_ref(v_inst_1020_);
lean_dec_ref(v_inst_1019_);
v___x_1051_ = lean_apply_1(v_modifyEnv_1017_, v___f_1018_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___y_1054_; 
lean_dec_ref(v___f_1018_);
lean_dec(v_modifyEnv_1017_);
v___x_1052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
if (v_isExporting_1029_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12));
v___y_1054_ = v___x_1061_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13));
v___y_1054_ = v___x_1062_;
goto v___jp_1053_;
}
v___jp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_inc_ref(v___y_1054_);
v___x_1055_ = l_Lean_stringToMessageData(v___y_1054_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1052_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
if (v_isMeta_1028_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10));
v___y_1038_ = v___x_1058_;
v___y_1039_ = v___x_1059_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11));
v___y_1038_ = v___x_1058_;
v___y_1039_ = v___x_1060_;
goto v___jp_1037_;
}
}
}
v___jp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___y_1032_);
lean_ctor_set(v___x_1034_, 1, v___y_1033_);
v___x_1035_ = l_Lean_addTrace___redArg(v_inst_1019_, v_inst_1020_, v_inst_1021_, v_inst_1022_, v_cls_1023_, v___x_1034_);
v___x_1036_ = lean_apply_4(v_toBind_1024_, lean_box(0), lean_box(0), v___x_1035_, v___f_1025_);
return v___x_1036_;
}
v___jp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
lean_inc_ref(v___y_1039_);
v___x_1040_ = l_Lean_stringToMessageData(v___y_1039_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___y_1038_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_MessageData_ofName(v_mod_1026_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_Name_isAnonymous(v_hint_1027_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
v___x_1048_ = l_Lean_MessageData_ofName(v_hint_1027_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___y_1032_ = v___x_1045_;
v___y_1033_ = v___x_1049_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1050_; 
lean_dec(v_hint_1027_);
v___x_1050_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
v___y_1032_ = v___x_1045_;
v___y_1033_ = v___x_1050_;
goto v___jp_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_modifyEnv_1063_, lean_object* v___f_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_cls_1069_, lean_object* v_toBind_1070_, lean_object* v___f_1071_, lean_object* v_mod_1072_, lean_object* v_hint_1073_, lean_object* v_isMeta_1074_, lean_object* v_isExporting_1075_, lean_object* v_____do__lift_1076_){
_start:
{
uint8_t v_isMeta_boxed_1077_; uint8_t v_isExporting_boxed_1078_; uint8_t v_____do__lift_961__boxed_1079_; lean_object* v_res_1080_; 
v_isMeta_boxed_1077_ = lean_unbox(v_isMeta_1074_);
v_isExporting_boxed_1078_ = lean_unbox(v_isExporting_1075_);
v_____do__lift_961__boxed_1079_ = lean_unbox(v_____do__lift_1076_);
v_res_1080_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_modifyEnv_1063_, v___f_1064_, v_inst_1065_, v_inst_1066_, v_inst_1067_, v_inst_1068_, v_cls_1069_, v_toBind_1070_, v___f_1071_, v_mod_1072_, v_hint_1073_, v_isMeta_boxed_1077_, v_isExporting_boxed_1078_, v_____do__lift_961__boxed_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v___x_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v_entry_1084_, lean_object* v_inst_1085_, lean_object* v_toApplicative_1086_, lean_object* v_modifyEnv_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_toBind_1091_, lean_object* v_mod_1092_, lean_object* v_hint_1093_, uint8_t v_isMeta_1094_, uint8_t v_isExporting_1095_, lean_object* v_inst_1096_, lean_object* v_____do__lift_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1098_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1099_ = lean_box(1);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1081_, v___x_1098_, v_____do__lift_1097_, v___x_1099_, v___x_1100_);
lean_inc_ref(v_entry_1084_);
v___x_1102_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1082_, v___x_1083_, v___x_1101_, v_entry_1084_);
if (v___x_1102_ == 0)
{
lean_object* v_getInheritedTraceOptions_1103_; lean_object* v_toPure_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v_cls_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_getInheritedTraceOptions_1103_ = lean_ctor_get(v_inst_1085_, 2);
lean_inc(v_getInheritedTraceOptions_1103_);
v_toPure_1104_ = lean_ctor_get(v_toApplicative_1086_, 1);
lean_inc(v_toPure_1104_);
lean_dec_ref(v_toApplicative_1086_);
v___f_1105_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1105_, 0, v___x_1098_);
lean_closure_set(v___f_1105_, 1, v_entry_1084_);
lean_closure_set(v___f_1105_, 2, v___x_1100_);
lean_inc_ref(v___f_1105_);
lean_inc(v_modifyEnv_1087_);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1106_, 0, v_modifyEnv_1087_);
lean_closure_set(v___f_1106_, 1, v___f_1105_);
v_cls_1107_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1108_ = lean_box(v_isMeta_1094_);
v___x_1109_ = lean_box(v_isExporting_1095_);
lean_inc_n(v_toBind_1091_, 3);
v___f_1110_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1110_, 0, v_modifyEnv_1087_);
lean_closure_set(v___f_1110_, 1, v___f_1105_);
lean_closure_set(v___f_1110_, 2, v_inst_1088_);
lean_closure_set(v___f_1110_, 3, v_inst_1085_);
lean_closure_set(v___f_1110_, 4, v_inst_1089_);
lean_closure_set(v___f_1110_, 5, v_inst_1090_);
lean_closure_set(v___f_1110_, 6, v_cls_1107_);
lean_closure_set(v___f_1110_, 7, v_toBind_1091_);
lean_closure_set(v___f_1110_, 8, v___f_1106_);
lean_closure_set(v___f_1110_, 9, v_mod_1092_);
lean_closure_set(v___f_1110_, 10, v_hint_1093_);
lean_closure_set(v___f_1110_, 11, v___x_1108_);
lean_closure_set(v___f_1110_, 12, v___x_1109_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1111_, 0, v_toPure_1104_);
lean_closure_set(v___f_1111_, 1, v_cls_1107_);
lean_closure_set(v___f_1111_, 2, v_toBind_1091_);
lean_closure_set(v___f_1111_, 3, v_inst_1096_);
v___x_1112_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1103_, v___f_1111_);
v___x_1113_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1112_, v___f_1110_);
return v___x_1113_;
}
else
{
lean_object* v_toPure_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_inst_1096_);
lean_dec(v_hint_1093_);
lean_dec(v_mod_1092_);
lean_dec(v_toBind_1091_);
lean_dec(v_inst_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_inst_1088_);
lean_dec(v_modifyEnv_1087_);
lean_dec_ref(v_inst_1085_);
lean_dec_ref(v_entry_1084_);
v_toPure_1114_ = lean_ctor_get(v_toApplicative_1086_, 1);
lean_inc(v_toPure_1114_);
lean_dec_ref(v_toApplicative_1086_);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_apply_2(v_toPure_1114_, lean_box(0), v___x_1115_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1117_ = _args[0];
lean_object* v___x_1118_ = _args[1];
lean_object* v___x_1119_ = _args[2];
lean_object* v_entry_1120_ = _args[3];
lean_object* v_inst_1121_ = _args[4];
lean_object* v_toApplicative_1122_ = _args[5];
lean_object* v_modifyEnv_1123_ = _args[6];
lean_object* v_inst_1124_ = _args[7];
lean_object* v_inst_1125_ = _args[8];
lean_object* v_inst_1126_ = _args[9];
lean_object* v_toBind_1127_ = _args[10];
lean_object* v_mod_1128_ = _args[11];
lean_object* v_hint_1129_ = _args[12];
lean_object* v_isMeta_1130_ = _args[13];
lean_object* v_isExporting_1131_ = _args[14];
lean_object* v_inst_1132_ = _args[15];
lean_object* v_____do__lift_1133_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1134_; uint8_t v_isExporting_boxed_1135_; lean_object* v_res_1136_; 
v_isMeta_boxed_1134_ = lean_unbox(v_isMeta_1130_);
v_isExporting_boxed_1135_ = lean_unbox(v_isExporting_1131_);
v_res_1136_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v___x_1117_, v___x_1118_, v___x_1119_, v_entry_1120_, v_inst_1121_, v_toApplicative_1122_, v_modifyEnv_1123_, v_inst_1124_, v_inst_1125_, v_inst_1126_, v_toBind_1127_, v_mod_1128_, v_hint_1129_, v_isMeta_boxed_1134_, v_isExporting_boxed_1135_, v_inst_1132_, v_____do__lift_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v_mod_1137_, uint8_t v_isMeta_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v_inst_1142_, lean_object* v_toApplicative_1143_, lean_object* v_modifyEnv_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_toBind_1148_, lean_object* v_hint_1149_, lean_object* v_inst_1150_, lean_object* v_getEnv_1151_, lean_object* v_____do__lift_1152_){
_start:
{
uint8_t v_isExporting_1153_; lean_object* v_entry_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; 
v_isExporting_1153_ = lean_ctor_get_uint8(v_____do__lift_1152_, sizeof(void*)*8);
lean_inc(v_mod_1137_);
v_entry_1154_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1154_, 0, v_mod_1137_);
lean_ctor_set_uint8(v_entry_1154_, sizeof(void*)*1, v_isExporting_1153_);
lean_ctor_set_uint8(v_entry_1154_, sizeof(void*)*1 + 1, v_isMeta_1138_);
v___x_1155_ = lean_box(v_isMeta_1138_);
v___x_1156_ = lean_box(v_isExporting_1153_);
lean_inc(v_toBind_1148_);
v___f_1157_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1157_, 0, v___x_1139_);
lean_closure_set(v___f_1157_, 1, v___x_1140_);
lean_closure_set(v___f_1157_, 2, v___x_1141_);
lean_closure_set(v___f_1157_, 3, v_entry_1154_);
lean_closure_set(v___f_1157_, 4, v_inst_1142_);
lean_closure_set(v___f_1157_, 5, v_toApplicative_1143_);
lean_closure_set(v___f_1157_, 6, v_modifyEnv_1144_);
lean_closure_set(v___f_1157_, 7, v_inst_1145_);
lean_closure_set(v___f_1157_, 8, v_inst_1146_);
lean_closure_set(v___f_1157_, 9, v_inst_1147_);
lean_closure_set(v___f_1157_, 10, v_toBind_1148_);
lean_closure_set(v___f_1157_, 11, v_mod_1137_);
lean_closure_set(v___f_1157_, 12, v_hint_1149_);
lean_closure_set(v___f_1157_, 13, v___x_1155_);
lean_closure_set(v___f_1157_, 14, v___x_1156_);
lean_closure_set(v___f_1157_, 15, v_inst_1150_);
v___x_1158_ = lean_apply_4(v_toBind_1148_, lean_box(0), lean_box(0), v_getEnv_1151_, v___f_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object* v_mod_1159_, lean_object* v_isMeta_1160_, lean_object* v___x_1161_, lean_object* v___x_1162_, lean_object* v___x_1163_, lean_object* v_inst_1164_, lean_object* v_toApplicative_1165_, lean_object* v_modifyEnv_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_toBind_1170_, lean_object* v_hint_1171_, lean_object* v_inst_1172_, lean_object* v_getEnv_1173_, lean_object* v_____do__lift_1174_){
_start:
{
uint8_t v_isMeta_boxed_1175_; lean_object* v_res_1176_; 
v_isMeta_boxed_1175_ = lean_unbox(v_isMeta_1160_);
v_res_1176_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v_mod_1159_, v_isMeta_boxed_1175_, v___x_1161_, v___x_1162_, v___x_1163_, v_inst_1164_, v_toApplicative_1165_, v_modifyEnv_1166_, v_inst_1167_, v_inst_1168_, v_inst_1169_, v_toBind_1170_, v_hint_1171_, v_inst_1172_, v_getEnv_1173_, v_____do__lift_1174_);
lean_dec_ref(v_____do__lift_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_mod_1183_, uint8_t v_isMeta_1184_, lean_object* v_hint_1185_){
_start:
{
lean_object* v_toApplicative_1186_; lean_object* v_toBind_1187_; lean_object* v_getEnv_1188_; lean_object* v_modifyEnv_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
v_toApplicative_1186_ = lean_ctor_get(v_inst_1177_, 0);
lean_inc_ref(v_toApplicative_1186_);
v_toBind_1187_ = lean_ctor_get(v_inst_1177_, 1);
lean_inc_n(v_toBind_1187_, 2);
v_getEnv_1188_ = lean_ctor_get(v_inst_1178_, 0);
lean_inc_n(v_getEnv_1188_, 2);
v_modifyEnv_1189_ = lean_ctor_get(v_inst_1178_, 1);
lean_inc(v_modifyEnv_1189_);
lean_dec_ref(v_inst_1178_);
v___x_1190_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1191_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1192_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1193_ = lean_box(v_isMeta_1184_);
v___f_1194_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 16, 15);
lean_closure_set(v___f_1194_, 0, v_mod_1183_);
lean_closure_set(v___f_1194_, 1, v___x_1193_);
lean_closure_set(v___f_1194_, 2, v___x_1192_);
lean_closure_set(v___f_1194_, 3, v___x_1190_);
lean_closure_set(v___f_1194_, 4, v___x_1191_);
lean_closure_set(v___f_1194_, 5, v_inst_1179_);
lean_closure_set(v___f_1194_, 6, v_toApplicative_1186_);
lean_closure_set(v___f_1194_, 7, v_modifyEnv_1189_);
lean_closure_set(v___f_1194_, 8, v_inst_1177_);
lean_closure_set(v___f_1194_, 9, v_inst_1181_);
lean_closure_set(v___f_1194_, 10, v_inst_1182_);
lean_closure_set(v___f_1194_, 11, v_toBind_1187_);
lean_closure_set(v___f_1194_, 12, v_hint_1185_);
lean_closure_set(v___f_1194_, 13, v_inst_1180_);
lean_closure_set(v___f_1194_, 14, v_getEnv_1188_);
v___x_1195_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v_getEnv_1188_, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_mod_1202_, lean_object* v_isMeta_1203_, lean_object* v_hint_1204_){
_start:
{
uint8_t v_isMeta_boxed_1205_; lean_object* v_res_1206_; 
v_isMeta_boxed_1205_ = lean_unbox(v_isMeta_1203_);
v_res_1206_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1196_, v_inst_1197_, v_inst_1198_, v_inst_1199_, v_inst_1200_, v_inst_1201_, v_mod_1202_, v_isMeta_boxed_1205_, v_hint_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_mod_1214_, uint8_t v_isMeta_1215_, lean_object* v_hint_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1208_, v_inst_1209_, v_inst_1210_, v_inst_1211_, v_inst_1212_, v_inst_1213_, v_mod_1214_, v_isMeta_1215_, v_hint_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_mod_1225_, lean_object* v_isMeta_1226_, lean_object* v_hint_1227_){
_start:
{
uint8_t v_isMeta_boxed_1228_; lean_object* v_res_1229_; 
v_isMeta_boxed_1228_ = lean_unbox(v_isMeta_1226_);
v_res_1229_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_mod_1225_, v_isMeta_boxed_1228_, v_hint_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, uint8_t v_isMeta_1237_, lean_object* v_toApplicative_1238_, lean_object* v_____do__lift_1239_){
_start:
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = l_Lean_Environment_mainModule(v_____do__lift_1239_);
v___x_1241_ = lean_name_eq(v_modName_1230_, v___x_1240_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v_toApplicative_1238_);
v___x_1242_ = lean_box(0);
v___x_1243_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_modName_1230_, v_isMeta_1237_, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v_toPure_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_inst_1236_);
lean_dec_ref(v_inst_1235_);
lean_dec(v_inst_1234_);
lean_dec_ref(v_inst_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec(v_modName_1230_);
v_toPure_1244_ = lean_ctor_get(v_toApplicative_1238_, 1);
lean_inc(v_toPure_1244_);
lean_dec_ref(v_toApplicative_1238_);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_apply_2(v_toPure_1244_, lean_box(0), v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_isMeta_1254_, lean_object* v_toApplicative_1255_, lean_object* v_____do__lift_1256_){
_start:
{
uint8_t v_isMeta_boxed_1257_; lean_object* v_res_1258_; 
v_isMeta_boxed_1257_ = lean_unbox(v_isMeta_1254_);
v_res_1258_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_inst_1251_, v_inst_1252_, v_inst_1253_, v_isMeta_boxed_1257_, v_toApplicative_1255_, v_____do__lift_1256_);
lean_dec_ref(v_____do__lift_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_modName_1265_, uint8_t v_isMeta_1266_){
_start:
{
lean_object* v_toApplicative_1267_; lean_object* v_toBind_1268_; lean_object* v_getEnv_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; 
v_toApplicative_1267_ = lean_ctor_get(v_inst_1259_, 0);
lean_inc_ref(v_toApplicative_1267_);
v_toBind_1268_ = lean_ctor_get(v_inst_1259_, 1);
lean_inc(v_toBind_1268_);
v_getEnv_1269_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc(v_getEnv_1269_);
v___x_1270_ = lean_box(v_isMeta_1266_);
v___f_1271_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1271_, 0, v_modName_1265_);
lean_closure_set(v___f_1271_, 1, v_inst_1259_);
lean_closure_set(v___f_1271_, 2, v_inst_1260_);
lean_closure_set(v___f_1271_, 3, v_inst_1261_);
lean_closure_set(v___f_1271_, 4, v_inst_1262_);
lean_closure_set(v___f_1271_, 5, v_inst_1263_);
lean_closure_set(v___f_1271_, 6, v_inst_1264_);
lean_closure_set(v___f_1271_, 7, v___x_1270_);
lean_closure_set(v___f_1271_, 8, v_toApplicative_1267_);
v___x_1272_ = lean_apply_4(v_toBind_1268_, lean_box(0), lean_box(0), v_getEnv_1269_, v___f_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_modName_1279_, lean_object* v_isMeta_1280_){
_start:
{
uint8_t v_isMeta_boxed_1281_; lean_object* v_res_1282_; 
v_isMeta_boxed_1281_ = lean_unbox(v_isMeta_1280_);
v_res_1282_ = l_Lean_recordExtraModUse___redArg(v_inst_1273_, v_inst_1274_, v_inst_1275_, v_inst_1276_, v_inst_1277_, v_inst_1278_, v_modName_1279_, v_isMeta_boxed_1281_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_modName_1290_, uint8_t v_isMeta_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_recordExtraModUse___redArg(v_inst_1284_, v_inst_1285_, v_inst_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v_modName_1290_, v_isMeta_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_modName_1300_, lean_object* v_isMeta_1301_){
_start:
{
uint8_t v_isMeta_boxed_1302_; lean_object* v_res_1303_; 
v_isMeta_boxed_1302_ = lean_unbox(v_isMeta_1301_);
v_res_1303_ = l_Lean_recordExtraModUse(v_m_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_, v_inst_1298_, v_inst_1299_, v_modName_1300_, v_isMeta_boxed_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1304_, lean_object* v_____s_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_apply_2(v_toPure_1304_, lean_box(0), v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1308_, lean_object* v_toPure_1309_, lean_object* v_r_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1308_);
v___x_1312_ = lean_apply_2(v_toPure_1309_, lean_box(0), v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1313_, lean_object* v___x_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_declName_1321_, lean_object* v_toBind_1322_, lean_object* v___f_1323_, lean_object* v_a_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v_modules_1328_; lean_object* v___x_1329_; lean_object* v_toImport_1330_; lean_object* v_module_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1327_ = l_Lean_Environment_header(v_env_1313_);
v_modules_1328_ = lean_ctor_get(v___x_1327_, 3);
lean_inc_ref(v_modules_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = lean_array_get(v___x_1314_, v_modules_1328_, v_a_1324_);
lean_dec_ref(v_modules_1328_);
v_toImport_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_toImport_1330_);
lean_dec(v___x_1329_);
v_module_1331_ = lean_ctor_get(v_toImport_1330_, 0);
lean_inc(v_module_1331_);
lean_dec_ref(v_toImport_1330_);
v___x_1332_ = 0;
v___x_1333_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_module_1331_, v___x_1332_, v_declName_1321_);
v___x_1334_ = lean_apply_4(v_toBind_1322_, lean_box(0), lean_box(0), v___x_1333_, v___f_1323_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1335_, lean_object* v___x_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_declName_1343_, lean_object* v_toBind_1344_, lean_object* v___f_1345_, lean_object* v_a_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1335_, v___x_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_inst_1341_, v_inst_1342_, v_declName_1343_, v_toBind_1344_, v___f_1345_, v_a_1346_, v_x_1347_, v___y_1348_);
lean_dec(v_a_1346_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_env_1335_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1350_, lean_object* v_env_1351_, lean_object* v___x_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_declName_1359_, lean_object* v_toBind_1360_, lean_object* v___f_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v_____r_1365_){
_start:
{
lean_object* v___y_1367_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1375_ = l_Lean_indirectModUseExt;
v___x_1376_ = lean_box(1);
v___x_1377_ = lean_box(0);
lean_inc_ref(v_env_1351_);
v___x_1378_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1362_, v___x_1375_, v_env_1351_, v___x_1376_, v___x_1377_);
lean_inc(v_declName_1359_);
v___x_1379_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1363_, v___x_1364_, v___x_1378_, v_declName_1359_);
lean_dec(v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1367_ = v___x_1380_;
goto v___jp_1366_;
}
else
{
lean_object* v_val_1381_; 
v_val_1381_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1381_);
lean_dec_ref(v___x_1379_);
v___y_1367_ = v_val_1381_;
goto v___jp_1366_;
}
v___jp_1366_:
{
lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___f_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1368_ = lean_box(0);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1369_, 0, v___x_1368_);
lean_closure_set(v___f_1369_, 1, v_toPure_1350_);
lean_inc(v_toBind_1360_);
lean_inc_ref(v_inst_1353_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1370_, 0, v_env_1351_);
lean_closure_set(v___f_1370_, 1, v___x_1352_);
lean_closure_set(v___f_1370_, 2, v_inst_1353_);
lean_closure_set(v___f_1370_, 3, v_inst_1354_);
lean_closure_set(v___f_1370_, 4, v_inst_1355_);
lean_closure_set(v___f_1370_, 5, v_inst_1356_);
lean_closure_set(v___f_1370_, 6, v_inst_1357_);
lean_closure_set(v___f_1370_, 7, v_inst_1358_);
lean_closure_set(v___f_1370_, 8, v_declName_1359_);
lean_closure_set(v___f_1370_, 9, v_toBind_1360_);
lean_closure_set(v___f_1370_, 10, v___f_1369_);
v_sz_1371_ = lean_array_size(v___y_1367_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1353_, v___y_1367_, v___f_1370_, v_sz_1371_, v___x_1372_, v___x_1368_);
v___x_1374_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1373_, v___f_1361_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_declName_1389_, lean_object* v_toBind_1390_, lean_object* v___f_1391_, uint8_t v_isMeta_1392_, lean_object* v_____do__lift_1393_){
_start:
{
uint8_t v___y_1395_; 
if (v_isMeta_1392_ == 0)
{
lean_dec_ref(v_____do__lift_1393_);
v___y_1395_ = v_isMeta_1392_;
goto v___jp_1394_;
}
else
{
uint8_t v___x_1400_; 
lean_inc(v_declName_1389_);
v___x_1400_ = l_Lean_isMarkedMeta(v_____do__lift_1393_, v_declName_1389_);
if (v___x_1400_ == 0)
{
v___y_1395_ = v_isMeta_1392_;
goto v___jp_1394_;
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = 0;
v___y_1395_ = v___x_1401_;
goto v___jp_1394_;
}
}
v___jp_1394_:
{
lean_object* v_toImport_1396_; lean_object* v_module_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_toImport_1396_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_toImport_1396_);
lean_dec_ref(v___x_1382_);
v_module_1397_ = lean_ctor_get(v_toImport_1396_, 0);
lean_inc(v_module_1397_);
lean_dec_ref(v_toImport_1396_);
v___x_1398_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1383_, v_inst_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_module_1397_, v___y_1395_, v_declName_1389_);
v___x_1399_ = lean_apply_4(v_toBind_1390_, lean_box(0), lean_box(0), v___x_1398_, v___f_1391_);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_declName_1409_, lean_object* v_toBind_1410_, lean_object* v___f_1411_, lean_object* v_isMeta_1412_, lean_object* v_____do__lift_1413_){
_start:
{
uint8_t v_isMeta_boxed_1414_; lean_object* v_res_1415_; 
v_isMeta_boxed_1414_ = lean_unbox(v_isMeta_1412_);
v_res_1415_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_inst_1406_, v_inst_1407_, v_inst_1408_, v_declName_1409_, v_toBind_1410_, v___f_1411_, v_isMeta_boxed_1414_, v_____do__lift_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1416_, lean_object* v_declName_1417_, lean_object* v___x_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_toBind_1425_, lean_object* v___f_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, uint8_t v_isMeta_1430_, lean_object* v_getEnv_1431_, lean_object* v_env_1432_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1432_, v_declName_1417_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref(v_env_1432_);
lean_dec(v_getEnv_1431_);
lean_dec_ref(v___x_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v___x_1427_);
lean_dec(v___f_1426_);
lean_dec(v_toBind_1425_);
lean_dec(v_inst_1424_);
lean_dec_ref(v_inst_1423_);
lean_dec(v_inst_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v_inst_1420_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v___x_1418_);
lean_dec(v_declName_1417_);
goto v___jp_1433_;
}
else
{
lean_object* v_val_1437_; lean_object* v___x_1438_; lean_object* v_modules_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_val_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_val_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = l_Lean_Environment_header(v_env_1432_);
v_modules_1439_ = lean_ctor_get(v___x_1438_, 3);
lean_inc_ref(v_modules_1439_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = lean_array_get_size(v_modules_1439_);
v___x_1441_ = lean_nat_dec_lt(v_val_1437_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec_ref(v_modules_1439_);
lean_dec(v_val_1437_);
lean_dec_ref(v_env_1432_);
lean_dec(v_getEnv_1431_);
lean_dec_ref(v___x_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v___x_1427_);
lean_dec(v___f_1426_);
lean_dec(v_toBind_1425_);
lean_dec(v_inst_1424_);
lean_dec_ref(v_inst_1423_);
lean_dec(v_inst_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v_inst_1420_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v___x_1418_);
lean_dec(v_declName_1417_);
goto v___jp_1433_;
}
else
{
lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; 
lean_inc_n(v_toBind_1425_, 2);
lean_inc(v_declName_1417_);
lean_inc(v_inst_1424_);
lean_inc_ref(v_inst_1423_);
lean_inc(v_inst_1422_);
lean_inc_ref(v_inst_1421_);
lean_inc_ref(v_inst_1420_);
lean_inc_ref(v_inst_1419_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1442_, 0, v_toPure_1416_);
lean_closure_set(v___f_1442_, 1, v_env_1432_);
lean_closure_set(v___f_1442_, 2, v___x_1418_);
lean_closure_set(v___f_1442_, 3, v_inst_1419_);
lean_closure_set(v___f_1442_, 4, v_inst_1420_);
lean_closure_set(v___f_1442_, 5, v_inst_1421_);
lean_closure_set(v___f_1442_, 6, v_inst_1422_);
lean_closure_set(v___f_1442_, 7, v_inst_1423_);
lean_closure_set(v___f_1442_, 8, v_inst_1424_);
lean_closure_set(v___f_1442_, 9, v_declName_1417_);
lean_closure_set(v___f_1442_, 10, v_toBind_1425_);
lean_closure_set(v___f_1442_, 11, v___f_1426_);
lean_closure_set(v___f_1442_, 12, v___x_1427_);
lean_closure_set(v___f_1442_, 13, v___x_1428_);
lean_closure_set(v___f_1442_, 14, v___x_1429_);
v___x_1443_ = lean_array_fget(v_modules_1439_, v_val_1437_);
lean_dec(v_val_1437_);
lean_dec_ref(v_modules_1439_);
v___x_1444_ = lean_box(v_isMeta_1430_);
v___f_1445_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1445_, 0, v___x_1443_);
lean_closure_set(v___f_1445_, 1, v_inst_1419_);
lean_closure_set(v___f_1445_, 2, v_inst_1420_);
lean_closure_set(v___f_1445_, 3, v_inst_1421_);
lean_closure_set(v___f_1445_, 4, v_inst_1422_);
lean_closure_set(v___f_1445_, 5, v_inst_1423_);
lean_closure_set(v___f_1445_, 6, v_inst_1424_);
lean_closure_set(v___f_1445_, 7, v_declName_1417_);
lean_closure_set(v___f_1445_, 8, v_toBind_1425_);
lean_closure_set(v___f_1445_, 9, v___f_1442_);
lean_closure_set(v___f_1445_, 10, v___x_1444_);
v___x_1446_ = lean_apply_4(v_toBind_1425_, lean_box(0), lean_box(0), v_getEnv_1431_, v___f_1445_);
return v___x_1446_;
}
}
v___jp_1433_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_apply_2(v_toPure_1416_, lean_box(0), v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1447_ = _args[0];
lean_object* v_declName_1448_ = _args[1];
lean_object* v___x_1449_ = _args[2];
lean_object* v_inst_1450_ = _args[3];
lean_object* v_inst_1451_ = _args[4];
lean_object* v_inst_1452_ = _args[5];
lean_object* v_inst_1453_ = _args[6];
lean_object* v_inst_1454_ = _args[7];
lean_object* v_inst_1455_ = _args[8];
lean_object* v_toBind_1456_ = _args[9];
lean_object* v___f_1457_ = _args[10];
lean_object* v___x_1458_ = _args[11];
lean_object* v___x_1459_ = _args[12];
lean_object* v___x_1460_ = _args[13];
lean_object* v_isMeta_1461_ = _args[14];
lean_object* v_getEnv_1462_ = _args[15];
lean_object* v_env_1463_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1464_; lean_object* v_res_1465_; 
v_isMeta_boxed_1464_ = lean_unbox(v_isMeta_1461_);
v_res_1465_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1447_, v_declName_1448_, v___x_1449_, v_inst_1450_, v_inst_1451_, v_inst_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_toBind_1456_, v___f_1457_, v___x_1458_, v___x_1459_, v___x_1460_, v_isMeta_boxed_1464_, v_getEnv_1462_, v_env_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_declName_1472_, uint8_t v_isMeta_1473_){
_start:
{
lean_object* v_toApplicative_1474_; lean_object* v_toBind_1475_; lean_object* v_getEnv_1476_; lean_object* v_toPure_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; 
v_toApplicative_1474_ = lean_ctor_get(v_inst_1466_, 0);
v_toBind_1475_ = lean_ctor_get(v_inst_1466_, 1);
lean_inc_n(v_toBind_1475_, 2);
v_getEnv_1476_ = lean_ctor_get(v_inst_1467_, 0);
lean_inc_n(v_getEnv_1476_, 2);
v_toPure_1477_ = lean_ctor_get(v_toApplicative_1474_, 1);
lean_inc_n(v_toPure_1477_, 2);
v___x_1478_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1479_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1480_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1481_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1482_, 0, v_toPure_1477_);
v___x_1483_ = lean_box(v_isMeta_1473_);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1484_, 0, v_toPure_1477_);
lean_closure_set(v___f_1484_, 1, v_declName_1472_);
lean_closure_set(v___f_1484_, 2, v___x_1481_);
lean_closure_set(v___f_1484_, 3, v_inst_1466_);
lean_closure_set(v___f_1484_, 4, v_inst_1467_);
lean_closure_set(v___f_1484_, 5, v_inst_1468_);
lean_closure_set(v___f_1484_, 6, v_inst_1469_);
lean_closure_set(v___f_1484_, 7, v_inst_1470_);
lean_closure_set(v___f_1484_, 8, v_inst_1471_);
lean_closure_set(v___f_1484_, 9, v_toBind_1475_);
lean_closure_set(v___f_1484_, 10, v___f_1482_);
lean_closure_set(v___f_1484_, 11, v___x_1480_);
lean_closure_set(v___f_1484_, 12, v___x_1478_);
lean_closure_set(v___f_1484_, 13, v___x_1479_);
lean_closure_set(v___f_1484_, 14, v___x_1483_);
lean_closure_set(v___f_1484_, 15, v_getEnv_1476_);
v___x_1485_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v_getEnv_1476_, v___f_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_declName_1492_, lean_object* v_isMeta_1493_){
_start:
{
uint8_t v_isMeta_boxed_1494_; lean_object* v_res_1495_; 
v_isMeta_boxed_1494_ = lean_unbox(v_isMeta_1493_);
v_res_1495_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1486_, v_inst_1487_, v_inst_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_declName_1492_, v_isMeta_boxed_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_declName_1503_, uint8_t v_isMeta_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1497_, v_inst_1498_, v_inst_1499_, v_inst_1500_, v_inst_1501_, v_inst_1502_, v_declName_1503_, v_isMeta_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_declName_1513_, lean_object* v_isMeta_1514_){
_start:
{
uint8_t v_isMeta_boxed_1515_; lean_object* v_res_1516_; 
v_isMeta_boxed_1515_ = lean_unbox(v_isMeta_1514_);
v_res_1516_ = l_Lean_recordExtraModUseFromDecl(v_m_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_declName_1513_, v_isMeta_boxed_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1517_, lean_object* v_e_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_box(0);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_box(0);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1522_);
lean_dec_ref(v_x_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_array_mk(v_es_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1542_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1544_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1548_, lean_object* v_modIdx_1549_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1550_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1551_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1552_ = 0;
v___x_1553_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1550_, v___x_1551_, v_env_1548_, v_modIdx_1549_, v___x_1552_);
v___x_1554_ = lean_array_get_size(v___x_1553_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
uint8_t v___x_1557_; 
v___x_1557_ = 1;
return v___x_1557_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = 0;
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1559_, lean_object* v_modIdx_1560_){
_start:
{
uint8_t v_res_1561_; lean_object* v_r_1562_; 
v_res_1561_ = l_Lean_isExtraRevModUse(v_env_1559_, v_modIdx_1560_);
lean_dec(v_modIdx_1560_);
lean_dec_ref(v_env_1559_);
v_r_1562_ = lean_box(v_res_1561_);
return v_r_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v_toEnvExtension_1565_; lean_object* v_asyncMode_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_toEnvExtension_1565_ = lean_ctor_get(v___x_1563_, 0);
v_asyncMode_1566_ = lean_ctor_get(v_toEnvExtension_1565_, 2);
lean_inc(v_asyncMode_1566_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_box(0);
v___x_1569_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1563_, v_x_1564_, v___x_1567_, v_asyncMode_1566_, v___x_1568_);
lean_dec(v_asyncMode_1566_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v_modifyEnv_1573_, lean_object* v___f_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_cls_1579_, lean_object* v_toBind_1580_, lean_object* v___f_1581_, uint8_t v_____do__lift_1582_){
_start:
{
if (v_____do__lift_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec(v___f_1581_);
lean_dec(v_toBind_1580_);
lean_dec(v_cls_1579_);
lean_dec(v_inst_1578_);
lean_dec_ref(v_inst_1577_);
lean_dec_ref(v_inst_1576_);
lean_dec_ref(v_inst_1575_);
v___x_1583_ = lean_apply_1(v_modifyEnv_1573_, v___f_1574_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v___f_1574_);
lean_dec(v_modifyEnv_1573_);
v___x_1584_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1);
v___x_1585_ = l_Lean_addTrace___redArg(v_inst_1575_, v_inst_1576_, v_inst_1577_, v_inst_1578_, v_cls_1579_, v___x_1584_);
v___x_1586_ = lean_apply_4(v_toBind_1580_, lean_box(0), lean_box(0), v___x_1585_, v___f_1581_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object* v_modifyEnv_1587_, lean_object* v___f_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_cls_1593_, lean_object* v_toBind_1594_, lean_object* v___f_1595_, lean_object* v_____do__lift_1596_){
_start:
{
uint8_t v_____do__lift_326__boxed_1597_; lean_object* v_res_1598_; 
v_____do__lift_326__boxed_1597_ = lean_unbox(v_____do__lift_1596_);
v_res_1598_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(v_modifyEnv_1587_, v___f_1588_, v_inst_1589_, v_inst_1590_, v_inst_1591_, v_inst_1592_, v_cls_1593_, v_toBind_1594_, v___f_1595_, v_____do__lift_326__boxed_1597_);
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___f_1600_; 
v___x_1599_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1600_, 0, v___x_1599_);
return v___f_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v___x_1601_, lean_object* v_toApplicative_1602_, lean_object* v_inst_1603_, lean_object* v_modifyEnv_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_toBind_1608_, lean_object* v_inst_1609_, lean_object* v_____do__lift_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1611_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1612_ = lean_box(1);
v___x_1613_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1601_, v___x_1611_, v_____do__lift_1610_, v___x_1612_);
v___x_1614_ = l_List_isEmpty___redArg(v___x_1613_);
lean_dec(v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v_toPure_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v_inst_1609_);
lean_dec(v_toBind_1608_);
lean_dec(v_inst_1607_);
lean_dec_ref(v_inst_1606_);
lean_dec_ref(v_inst_1605_);
lean_dec(v_modifyEnv_1604_);
lean_dec_ref(v_inst_1603_);
v_toPure_1615_ = lean_ctor_get(v_toApplicative_1602_, 1);
lean_inc(v_toPure_1615_);
lean_dec_ref(v_toApplicative_1602_);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_apply_2(v_toPure_1615_, lean_box(0), v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v_getInheritedTraceOptions_1618_; lean_object* v_toPure_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v_cls_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_getInheritedTraceOptions_1618_ = lean_ctor_get(v_inst_1603_, 2);
lean_inc(v_getInheritedTraceOptions_1618_);
v_toPure_1619_ = lean_ctor_get(v_toApplicative_1602_, 1);
lean_inc(v_toPure_1619_);
lean_dec_ref(v_toApplicative_1602_);
v___f_1620_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0);
lean_inc(v_modifyEnv_1604_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1621_, 0, v_modifyEnv_1604_);
lean_closure_set(v___f_1621_, 1, v___f_1620_);
v_cls_1622_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1608_, 3);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1623_, 0, v_modifyEnv_1604_);
lean_closure_set(v___f_1623_, 1, v___f_1620_);
lean_closure_set(v___f_1623_, 2, v_inst_1605_);
lean_closure_set(v___f_1623_, 3, v_inst_1603_);
lean_closure_set(v___f_1623_, 4, v_inst_1606_);
lean_closure_set(v___f_1623_, 5, v_inst_1607_);
lean_closure_set(v___f_1623_, 6, v_cls_1622_);
lean_closure_set(v___f_1623_, 7, v_toBind_1608_);
lean_closure_set(v___f_1623_, 8, v___f_1621_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1624_, 0, v_toPure_1619_);
lean_closure_set(v___f_1624_, 1, v_cls_1622_);
lean_closure_set(v___f_1624_, 2, v_toBind_1608_);
lean_closure_set(v___f_1624_, 3, v_inst_1609_);
v___x_1625_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1618_, v___f_1624_);
v___x_1626_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1625_, v___f_1623_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_){
_start:
{
lean_object* v_toApplicative_1633_; lean_object* v_toBind_1634_; lean_object* v_getEnv_1635_; lean_object* v_modifyEnv_1636_; lean_object* v___x_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; 
v_toApplicative_1633_ = lean_ctor_get(v_inst_1627_, 0);
lean_inc_ref(v_toApplicative_1633_);
v_toBind_1634_ = lean_ctor_get(v_inst_1627_, 1);
lean_inc_n(v_toBind_1634_, 2);
v_getEnv_1635_ = lean_ctor_get(v_inst_1628_, 0);
lean_inc(v_getEnv_1635_);
v_modifyEnv_1636_ = lean_ctor_get(v_inst_1628_, 1);
lean_inc(v_modifyEnv_1636_);
lean_dec_ref(v_inst_1628_);
v___x_1637_ = lean_box(0);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4), 10, 9);
lean_closure_set(v___f_1638_, 0, v___x_1637_);
lean_closure_set(v___f_1638_, 1, v_toApplicative_1633_);
lean_closure_set(v___f_1638_, 2, v_inst_1629_);
lean_closure_set(v___f_1638_, 3, v_modifyEnv_1636_);
lean_closure_set(v___f_1638_, 4, v_inst_1627_);
lean_closure_set(v___f_1638_, 5, v_inst_1631_);
lean_closure_set(v___f_1638_, 6, v_inst_1632_);
lean_closure_set(v___f_1638_, 7, v_toBind_1634_);
lean_closure_set(v___f_1638_, 8, v_inst_1630_);
v___x_1639_ = lean_apply_4(v_toBind_1634_, lean_box(0), lean_box(0), v_getEnv_1635_, v___f_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(4259277863u);
v___x_1680_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1681_ = l_Lean_Name_num___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1684_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1685_ = l_Lean_Name_str___override(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1689_ = l_Lean_Name_str___override(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_unsigned_to_nat(2u);
v___x_1691_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__17_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1692_ = l_Lean_Name_num___override(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1695_ = 0;
v___x_1696_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__18_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1697_ = l_Lean_registerTraceClass(v___x_1694_, v___x_1695_, v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1699_;
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
res = l_Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
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
