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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "indirectModUseExt"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 173, 36, 115, 222, 236, 117, 108)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object*);
static const lean_array_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ExtraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 69, 125, 143, 117, 200, 37, 103)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(163, 125, 98, 145, 27, 242, 139, 173)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 80, 45, 80, 85, 236, 79, 117)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 241, 212, 4, 163, 62, 5, 148)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
static lean_once_cell_t l_Lean_getExtraModUses___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__0;
static lean_once_cell_t l_Lean_getExtraModUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__1;
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isExtraRevModUseExt"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 81, 220, 33, 30, 172, 4, 212)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 211, 254, 26, 237, 216, 211, 30)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 203, 147, 114, 124, 159, 234, 194)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 198, 100, 78, 72, 145, 180, 196)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 126, 81, 65, 191, 6, 222, 76)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_array_mk(v_es_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_s_17_, lean_object* v_x_18_){
_start:
{
lean_inc_ref(v_s_17_);
return v_s_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_s_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_s_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_s_19_);
return v_res_21_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_22_; uint64_t v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1723u);
v___x_23_ = lean_uint64_of_nat(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
return v_x_24_;
}
else
{
lean_object* v_key_26_; lean_object* v_value_27_; lean_object* v_tail_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_54_; 
v_key_26_ = lean_ctor_get(v_x_25_, 0);
v_value_27_ = lean_ctor_get(v_x_25_, 1);
v_tail_28_ = lean_ctor_get(v_x_25_, 2);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_25_);
if (v_isSharedCheck_54_ == 0)
{
v___x_30_ = v_x_25_;
v_isShared_31_ = v_isSharedCheck_54_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_tail_28_);
lean_inc(v_value_27_);
lean_inc(v_key_26_);
lean_dec(v_x_25_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_54_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; uint64_t v___y_34_; 
v___x_32_ = lean_array_get_size(v_x_24_);
if (lean_obj_tag(v_key_26_) == 0)
{
uint64_t v___x_52_; 
v___x_52_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_34_ = v___x_52_;
goto v___jp_33_;
}
else
{
uint64_t v_hash_53_; 
v_hash_53_ = lean_ctor_get_uint64(v_key_26_, sizeof(void*)*2);
v___y_34_ = v_hash_53_;
goto v___jp_33_;
}
v___jp_33_:
{
uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v_fold_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; size_t v___x_44_; size_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_35_ = 32ULL;
v___x_36_ = lean_uint64_shift_right(v___y_34_, v___x_35_);
v_fold_37_ = lean_uint64_xor(v___y_34_, v___x_36_);
v___x_38_ = 16ULL;
v___x_39_ = lean_uint64_shift_right(v_fold_37_, v___x_38_);
v___x_40_ = lean_uint64_xor(v_fold_37_, v___x_39_);
v___x_41_ = lean_uint64_to_usize(v___x_40_);
v___x_42_ = lean_usize_of_nat(v___x_32_);
v___x_43_ = ((size_t)1ULL);
v___x_44_ = lean_usize_sub(v___x_42_, v___x_43_);
v___x_45_ = lean_usize_land(v___x_41_, v___x_44_);
v___x_46_ = lean_array_uget_borrowed(v_x_24_, v___x_45_);
lean_inc(v___x_46_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 2, v___x_46_);
v___x_48_ = v___x_30_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_key_26_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_value_27_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v___x_46_);
v___x_48_ = v_reuseFailAlloc_51_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; 
v___x_49_ = lean_array_uset(v_x_24_, v___x_45_, v___x_48_);
v_x_24_ = v___x_49_;
v_x_25_ = v_tail_28_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_55_, lean_object* v_source_56_, lean_object* v_target_57_){
_start:
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_array_get_size(v_source_56_);
v___x_59_ = lean_nat_dec_lt(v_i_55_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec_ref(v_source_56_);
lean_dec(v_i_55_);
return v_target_57_;
}
else
{
lean_object* v_es_60_; lean_object* v___x_61_; lean_object* v_source_62_; lean_object* v_target_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_es_60_ = lean_array_fget(v_source_56_, v_i_55_);
v___x_61_ = lean_box(0);
v_source_62_ = lean_array_fset(v_source_56_, v_i_55_, v___x_61_);
v_target_63_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_target_57_, v_es_60_);
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_i_55_, v___x_64_);
lean_dec(v_i_55_);
v_i_55_ = v___x_65_;
v_source_56_ = v_source_62_;
v_target_57_ = v_target_63_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_nbuckets_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_68_ = lean_array_get_size(v_data_67_);
v___x_69_ = lean_unsigned_to_nat(2u);
v_nbuckets_70_ = lean_nat_mul(v___x_68_, v___x_69_);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_box(0);
v___x_73_ = lean_mk_array(v_nbuckets_70_, v___x_72_);
v___x_74_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_71_, v_data_67_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object* v_val_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___y_80_; 
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_80_ = v___x_83_;
goto v___jp_79_;
}
else
{
lean_object* v_val_84_; 
v_val_84_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v_x_78_, 1);
v___y_80_ = v_val_84_;
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_array_push(v___y_80_, v_val_77_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_val_85_, lean_object* v_a_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_val_90_; lean_object* v___x_91_; 
v___x_88_ = lean_box(0);
v___x_89_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_85_, v___x_88_);
v_val_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_val_90_);
lean_dec(v___x_89_);
v___x_91_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_91_, 0, v_a_86_);
lean_ctor_set(v___x_91_, 1, v_val_90_);
lean_ctor_set(v___x_91_, 2, v_x_87_);
return v___x_91_;
}
else
{
lean_object* v_key_92_; lean_object* v_value_93_; lean_object* v_tail_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_109_; 
v_key_92_ = lean_ctor_get(v_x_87_, 0);
v_value_93_ = lean_ctor_get(v_x_87_, 1);
v_tail_94_ = lean_ctor_get(v_x_87_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_109_ == 0)
{
v___x_96_ = v_x_87_;
v_isShared_97_ = v_isSharedCheck_109_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_tail_94_);
lean_inc(v_value_93_);
lean_inc(v_key_92_);
lean_dec(v_x_87_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_109_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
uint8_t v___x_98_; 
v___x_98_ = lean_name_eq(v_key_92_, v_a_86_);
if (v___x_98_ == 0)
{
lean_object* v_tail_99_; lean_object* v___x_101_; 
v_tail_99_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_85_, v_a_86_, v_tail_94_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 2, v_tail_99_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_key_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_value_93_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_tail_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_val_105_; lean_object* v___x_107_; 
lean_dec(v_key_92_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_value_93_);
v___x_104_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_85_, v___x_103_);
v_val_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_val_105_);
lean_dec(v___x_104_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_val_105_);
lean_ctor_set(v___x_96_, 0, v_a_86_);
v___x_107_ = v___x_96_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_86_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_val_105_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_tail_94_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_110_, lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
else
{
lean_object* v_key_113_; lean_object* v_tail_114_; uint8_t v___x_115_; 
v_key_113_ = lean_ctor_get(v_x_111_, 0);
v_tail_114_ = lean_ctor_get(v_x_111_, 2);
v___x_115_ = lean_name_eq(v_key_113_, v_a_110_);
if (v___x_115_ == 0)
{
v_x_111_ = v_tail_114_;
goto _start;
}
else
{
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_117_, v_x_118_);
lean_dec(v_x_118_);
lean_dec(v_a_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_val_121_, lean_object* v_m_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___y_125_; size_t v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v_size_131_; lean_object* v_buckets_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_179_; 
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
v___x_129_ = lean_array_uset(v___y_127_, v___y_126_, v___y_125_);
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
v___x_177_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
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
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_123_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_size_x27_155_; lean_object* v___x_156_; lean_object* v_buckets_x27_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_152_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
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
v_val_164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_157_);
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
v_bkt_x27_173_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_121_, v_a_123_, v_bkt_150_);
v___x_174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_123_, v_bkt_x27_173_);
lean_dec(v_a_123_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_sub(v_size_131_, v___x_175_);
lean_dec(v_size_131_);
v___y_125_ = v_bkt_x27_173_;
v___y_126_ = v___x_149_;
v___y_127_ = v_buckets_x27_172_;
v___y_128_ = v___x_176_;
goto v___jp_124_;
}
else
{
v___y_125_ = v_bkt_x27_173_;
v___y_126_ = v___x_149_;
v___y_127_ = v_buckets_x27_172_;
v___y_128_ = v_size_131_;
goto v___jp_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_val_180_, lean_object* v_as_181_, size_t v_sz_182_, size_t v_i_183_, lean_object* v_b_184_){
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
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_180_, v_b_184_, v_declName_187_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_183_, v___x_189_);
v_i_183_ = v___x_190_;
v_b_184_ = v___x_188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_val_192_, lean_object* v_as_193_, lean_object* v_sz_194_, lean_object* v_i_195_, lean_object* v_b_196_){
_start:
{
size_t v_sz_boxed_197_; size_t v_i_boxed_198_; lean_object* v_res_199_; 
v_sz_boxed_197_ = lean_unbox_usize(v_sz_194_);
lean_dec(v_sz_194_);
v_i_boxed_198_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_192_, v_as_193_, v_sz_boxed_197_, v_i_boxed_198_, v_b_196_);
lean_dec_ref(v_as_193_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_as_200_, size_t v_sz_201_, size_t v_i_202_, lean_object* v_b_203_){
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
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_219_, v_a_223_, v_sz_228_, v___x_229_, v_fst_215_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_241_, lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_b_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_241_, v_sz_boxed_245_, v_i_boxed_246_, v_b_244_);
lean_dec_ref(v_as_241_);
return v_res_247_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_box(0);
v___x_249_ = lean_unsigned_to_nat(16u);
v___x_250_ = lean_mk_array(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_s_253_; 
v___x_251_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_252_ = lean_unsigned_to_nat(0u);
v_s_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_253_, 0, v___x_252_);
lean_ctor_set(v_s_253_, 1, v___x_251_);
return v_s_253_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_256_; lean_object* v_s_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_257_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_s_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_259_){
_start:
{
lean_object* v___x_260_; size_t v_sz_261_; size_t v___x_262_; lean_object* v___x_263_; lean_object* v_fst_264_; 
v___x_260_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_261_ = lean_array_size(v_es_259_);
v___x_262_ = ((size_t)0ULL);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_259_, v_sz_261_, v___x_262_, v___x_260_);
v_fst_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_fst_264_);
lean_dec_ref(v___x_263_);
return v_fst_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_265_);
lean_dec_ref(v_es_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_284_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_286_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_287_, lean_object* v_a_288_, lean_object* v_x_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_288_, v_x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_291_, lean_object* v_a_292_, lean_object* v_x_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_291_, v_a_292_, v_x_293_);
lean_dec(v_x_293_);
lean_dec(v_a_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_296_, lean_object* v_data_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_299_, lean_object* v_i_300_, lean_object* v_source_301_, lean_object* v_target_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_300_, v_source_301_, v_target_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_305_, v_x_306_);
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
uint8_t v_____do__lift_456__boxed_381_; lean_object* v_res_382_; 
v_____do__lift_456__boxed_381_ = lean_unbox(v_____do__lift_380_);
v_res_382_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_modifyEnv_369_, v___f_370_, v_declName_371_, v_kind_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_cls_377_, v_toBind_378_, v___f_379_, v_____do__lift_456__boxed_381_);
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
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v___x_413_, lean_object* v_kind_414_, lean_object* v_declName_415_, lean_object* v___x_416_, lean_object* v_toApplicative_417_, lean_object* v_inst_418_, lean_object* v_modifyEnv_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_toBind_423_, lean_object* v_inst_424_, lean_object* v_____do__lift_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; uint8_t v___x_431_; 
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
v___x_431_ = lean_bool_not(v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v_toPure_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref_known(v___x_429_, 2);
lean_dec(v_inst_424_);
lean_dec(v_toBind_423_);
lean_dec(v_inst_422_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
lean_dec(v_modifyEnv_419_);
lean_dec_ref(v_inst_418_);
lean_dec(v_declName_415_);
lean_dec_ref(v_kind_414_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_417_, 1);
lean_inc(v_toPure_432_);
lean_dec_ref(v_toApplicative_417_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_apply_2(v_toPure_432_, lean_box(0), v___x_433_);
return v___x_434_;
}
else
{
lean_object* v_getInheritedTraceOptions_435_; lean_object* v_toPure_436_; lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v_cls_439_; lean_object* v___f_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_getInheritedTraceOptions_435_ = lean_ctor_get(v_inst_418_, 2);
lean_inc(v_getInheritedTraceOptions_435_);
v_toPure_436_ = lean_ctor_get(v_toApplicative_417_, 1);
lean_inc(v_toPure_436_);
lean_dec_ref(v_toApplicative_417_);
v___f_437_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_437_, 0, v___x_426_);
lean_closure_set(v___f_437_, 1, v___x_429_);
lean_inc_ref(v___f_437_);
lean_inc(v_modifyEnv_419_);
v___f_438_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_438_, 0, v_modifyEnv_419_);
lean_closure_set(v___f_438_, 1, v___f_437_);
v_cls_439_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_423_, 3);
v___f_440_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_440_, 0, v_modifyEnv_419_);
lean_closure_set(v___f_440_, 1, v___f_437_);
lean_closure_set(v___f_440_, 2, v_declName_415_);
lean_closure_set(v___f_440_, 3, v_kind_414_);
lean_closure_set(v___f_440_, 4, v_inst_420_);
lean_closure_set(v___f_440_, 5, v_inst_418_);
lean_closure_set(v___f_440_, 6, v_inst_421_);
lean_closure_set(v___f_440_, 7, v_inst_422_);
lean_closure_set(v___f_440_, 8, v_cls_439_);
lean_closure_set(v___f_440_, 9, v_toBind_423_);
lean_closure_set(v___f_440_, 10, v___f_438_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_441_, 0, v_toPure_436_);
lean_closure_set(v___f_441_, 1, v_cls_439_);
lean_closure_set(v___f_441_, 2, v_toBind_423_);
lean_closure_set(v___f_441_, 3, v_inst_424_);
v___x_442_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_435_, v___f_441_);
v___x_443_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v___x_442_, v___f_440_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_kind_450_, lean_object* v_declName_451_){
_start:
{
lean_object* v_toApplicative_452_; lean_object* v_toBind_453_; lean_object* v_getEnv_454_; lean_object* v_modifyEnv_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___f_458_; lean_object* v___x_459_; 
v_toApplicative_452_ = lean_ctor_get(v_inst_444_, 0);
lean_inc_ref(v_toApplicative_452_);
v_toBind_453_ = lean_ctor_get(v_inst_444_, 1);
lean_inc_n(v_toBind_453_, 2);
v_getEnv_454_ = lean_ctor_get(v_inst_445_, 0);
lean_inc(v_getEnv_454_);
v_modifyEnv_455_ = lean_ctor_get(v_inst_445_, 1);
lean_inc(v_modifyEnv_455_);
lean_dec_ref(v_inst_445_);
v___x_456_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_457_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5), 13, 12);
lean_closure_set(v___f_458_, 0, v___x_457_);
lean_closure_set(v___f_458_, 1, v_kind_450_);
lean_closure_set(v___f_458_, 2, v_declName_451_);
lean_closure_set(v___f_458_, 3, v___x_456_);
lean_closure_set(v___f_458_, 4, v_toApplicative_452_);
lean_closure_set(v___f_458_, 5, v_inst_446_);
lean_closure_set(v___f_458_, 6, v_modifyEnv_455_);
lean_closure_set(v___f_458_, 7, v_inst_444_);
lean_closure_set(v___f_458_, 8, v_inst_448_);
lean_closure_set(v___f_458_, 9, v_inst_449_);
lean_closure_set(v___f_458_, 10, v_toBind_453_);
lean_closure_set(v___f_458_, 11, v_inst_447_);
v___x_459_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v_getEnv_454_, v___f_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_kind_467_, lean_object* v_declName_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_recordIndirectModUse___redArg(v_inst_461_, v_inst_462_, v_inst_463_, v_inst_464_, v_inst_465_, v_inst_466_, v_kind_467_, v_declName_468_);
return v___x_469_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_module_472_; uint8_t v_isExported_473_; uint8_t v_isMeta_474_; lean_object* v_module_475_; uint8_t v_isExported_476_; uint8_t v_isMeta_477_; uint8_t v___y_479_; uint8_t v___x_480_; 
v_module_472_ = lean_ctor_get(v_x_470_, 0);
v_isExported_473_ = lean_ctor_get_uint8(v_x_470_, sizeof(void*)*1);
v_isMeta_474_ = lean_ctor_get_uint8(v_x_470_, sizeof(void*)*1 + 1);
v_module_475_ = lean_ctor_get(v_x_471_, 0);
v_isExported_476_ = lean_ctor_get_uint8(v_x_471_, sizeof(void*)*1);
v_isMeta_477_ = lean_ctor_get_uint8(v_x_471_, sizeof(void*)*1 + 1);
v___x_480_ = lean_name_eq(v_module_472_, v_module_475_);
if (v___x_480_ == 0)
{
return v___x_480_;
}
else
{
if (v_isExported_473_ == 0)
{
if (v_isExported_476_ == 0)
{
v___y_479_ = v___x_480_;
goto v___jp_478_;
}
else
{
return v_isExported_473_;
}
}
else
{
v___y_479_ = v_isExported_476_;
goto v___jp_478_;
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
return v___y_479_;
}
else
{
if (v_isMeta_474_ == 0)
{
if (v_isMeta_477_ == 0)
{
return v___y_479_;
}
else
{
return v_isMeta_474_;
}
}
else
{
return v_isMeta_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_Lean_instBEqExtraModUse_beq(v_x_481_, v_x_482_);
lean_dec_ref(v_x_482_);
lean_dec_ref(v_x_481_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_487_){
_start:
{
lean_object* v_module_488_; uint8_t v_isExported_489_; uint8_t v_isMeta_490_; uint64_t v___y_492_; uint64_t v___y_493_; uint64_t v___x_499_; uint64_t v___y_501_; 
v_module_488_ = lean_ctor_get(v_x_487_, 0);
v_isExported_489_ = lean_ctor_get_uint8(v_x_487_, sizeof(void*)*1);
v_isMeta_490_ = lean_ctor_get_uint8(v_x_487_, sizeof(void*)*1 + 1);
v___x_499_ = 0ULL;
if (lean_obj_tag(v_module_488_) == 0)
{
uint64_t v___x_505_; 
v___x_505_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_501_ = v___x_505_;
goto v___jp_500_;
}
else
{
uint64_t v_hash_506_; 
v_hash_506_ = lean_ctor_get_uint64(v_module_488_, sizeof(void*)*2);
v___y_501_ = v_hash_506_;
goto v___jp_500_;
}
v___jp_491_:
{
uint64_t v___x_494_; 
v___x_494_ = lean_uint64_mix_hash(v___y_492_, v___y_493_);
if (v_isMeta_490_ == 0)
{
uint64_t v___x_495_; uint64_t v___x_496_; 
v___x_495_ = 13ULL;
v___x_496_ = lean_uint64_mix_hash(v___x_494_, v___x_495_);
return v___x_496_;
}
else
{
uint64_t v___x_497_; uint64_t v___x_498_; 
v___x_497_ = 11ULL;
v___x_498_ = lean_uint64_mix_hash(v___x_494_, v___x_497_);
return v___x_498_;
}
}
v___jp_500_:
{
uint64_t v___x_502_; 
v___x_502_ = lean_uint64_mix_hash(v___x_499_, v___y_501_);
if (v_isExported_489_ == 0)
{
uint64_t v___x_503_; 
v___x_503_ = 13ULL;
v___y_492_ = v___x_502_;
v___y_493_ = v___x_503_;
goto v___jp_491_;
}
else
{
uint64_t v___x_504_; 
v___x_504_ = 11ULL;
v___y_492_ = v___x_502_;
v___y_493_ = v___x_504_;
goto v___jp_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_507_){
_start:
{
uint64_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Lean_instHashableExtraModUse_hash(v_x_507_);
lean_dec_ref(v_x_507_);
v_r_509_ = lean_box_uint64(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_nat_to_int(v_a_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(10u);
v___x_528_ = lean_nat_to_int(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(14u);
v___x_536_ = lean_nat_to_int(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_542_ = lean_string_length(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_544_ = lean_nat_to_int(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_549_){
_start:
{
lean_object* v_module_550_; uint8_t v_isExported_551_; uint8_t v_isMeta_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_module_550_ = lean_ctor_get(v_x_549_, 0);
lean_inc(v_module_550_);
v_isExported_551_ = lean_ctor_get_uint8(v_x_549_, sizeof(void*)*1);
v_isMeta_552_ = lean_ctor_get_uint8(v_x_549_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_549_);
v___x_553_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_554_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_555_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Lean_Name_reprPrec(v_module_550_, v___x_556_);
v___x_558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_555_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = 0;
v___x_560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*1, v___x_559_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_554_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_box(1);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_553_);
v___x_569_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_570_ = l_Bool_repr___redArg(v_isExported_551_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_559_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_568_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_562_);
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_564_);
v___x_576_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_553_);
v___x_579_ = l_Bool_repr___redArg(v_isMeta_552_);
v___x_580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_555_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*1, v___x_559_);
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_578_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_584_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_582_);
v___x_586_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_583_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*1, v___x_559_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_590_, lean_object* v_prec_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_593_, lean_object* v_prec_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_instReprExtraModUse_repr(v_x_593_, v_prec_594_);
lean_dec(v_prec_594_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_598_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_entries_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_609_ = lean_array_mk(v_entries_607_);
v___x_610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_entries_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_611_, v_x_612_, v_entries_613_);
lean_dec_ref(v_x_612_);
lean_dec_ref(v_x_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_array_mk(v_es_615_);
return v___x_616_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_box(0));
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_620_);
lean_dec_ref(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_ks_626_; lean_object* v_vs_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_651_; 
v_ks_626_ = lean_ctor_get(v_x_622_, 0);
v_vs_627_ = lean_ctor_get(v_x_622_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_651_ == 0)
{
v___x_629_ = v_x_622_;
v_isShared_630_ = v_isSharedCheck_651_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_vs_627_);
lean_inc(v_ks_626_);
lean_dec(v_x_622_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_651_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_array_get_size(v_ks_626_);
v___x_632_ = lean_nat_dec_lt(v_x_623_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_x_623_);
v___x_633_ = lean_array_push(v_ks_626_, v_x_624_);
v___x_634_ = lean_array_push(v_vs_627_, v_x_625_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_634_);
lean_ctor_set(v___x_629_, 0, v___x_633_);
v___x_636_ = v___x_629_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v_k_x27_638_; uint8_t v___x_639_; 
v_k_x27_638_ = lean_array_fget_borrowed(v_ks_626_, v_x_623_);
v___x_639_ = l_Lean_instBEqExtraModUse_beq(v_x_624_, v_k_x27_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_641_; 
if (v_isShared_630_ == 0)
{
v___x_641_ = v___x_629_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_ks_626_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_vs_627_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_x_623_, v___x_642_);
lean_dec(v_x_623_);
v_x_622_ = v___x_641_;
v_x_623_ = v___x_643_;
goto _start;
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = lean_array_fset(v_ks_626_, v_x_623_, v_x_624_);
v___x_647_ = lean_array_fset(v_vs_627_, v_x_623_, v_x_625_);
lean_dec(v_x_623_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_647_);
lean_ctor_set(v___x_629_, 0, v___x_646_);
v___x_649_ = v___x_629_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_652_, lean_object* v_k_653_, lean_object* v_v_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_652_, v___x_655_, v_k_653_, v_v_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_658_, size_t v_x_659_, size_t v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_es_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v_j_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_es_663_ = lean_ctor_get(v_x_658_, 0);
v___x_664_ = ((size_t)31ULL);
v___x_665_ = lean_usize_land(v_x_659_, v___x_664_);
v_j_666_ = lean_usize_to_nat(v___x_665_);
v___x_667_ = lean_array_get_size(v_es_663_);
v___x_668_ = lean_nat_dec_lt(v_j_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_j_666_);
lean_dec(v_x_662_);
lean_dec_ref(v_x_661_);
return v_x_658_;
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_es_663_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_x_658_, 0);
lean_dec(v_unused_708_);
v___x_670_ = v_x_658_;
v_isShared_671_ = v_isSharedCheck_707_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_x_658_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_707_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_v_672_; lean_object* v___x_673_; lean_object* v_xs_x27_674_; lean_object* v___y_676_; 
v_v_672_ = lean_array_fget(v_es_663_, v_j_666_);
v___x_673_ = lean_box(0);
v_xs_x27_674_ = lean_array_fset(v_es_663_, v_j_666_, v___x_673_);
switch(lean_obj_tag(v_v_672_))
{
case 0:
{
lean_object* v_key_681_; lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_key_681_ = lean_ctor_get(v_v_672_, 0);
v_val_682_ = lean_ctor_get(v_v_672_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_v_672_);
if (v_isSharedCheck_692_ == 0)
{
v___x_684_ = v_v_672_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_inc(v_key_681_);
lean_dec(v_v_672_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_instBEqExtraModUse_beq(v_x_661_, v_key_681_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_del_object(v___x_684_);
v___x_687_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_681_, v_val_682_, v_x_661_, v_x_662_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___y_676_ = v___x_688_;
goto v___jp_675_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_val_682_);
lean_dec(v_key_681_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_x_662_);
lean_ctor_set(v___x_684_, 0, v_x_661_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_x_662_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_676_ = v___x_690_;
goto v___jp_675_;
}
}
}
}
case 1:
{
lean_object* v_node_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_705_; 
v_node_693_ = lean_ctor_get(v_v_672_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_v_672_);
if (v_isSharedCheck_705_ == 0)
{
v___x_695_ = v_v_672_;
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_node_693_);
lean_dec(v_v_672_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_697_ = ((size_t)5ULL);
v___x_698_ = lean_usize_shift_right(v_x_659_, v___x_697_);
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_x_660_, v___x_699_);
v___x_701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_693_, v___x_698_, v___x_700_, v_x_661_, v_x_662_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_701_);
v___x_703_ = v___x_695_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_676_ = v___x_703_;
goto v___jp_675_;
}
}
}
default: 
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_x_661_);
lean_ctor_set(v___x_706_, 1, v_x_662_);
v___y_676_ = v___x_706_;
goto v___jp_675_;
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_array_fset(v_xs_x27_674_, v_j_666_, v___y_676_);
lean_dec(v_j_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_677_);
v___x_679_ = v___x_670_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v_ks_709_; lean_object* v_vs_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_730_; 
v_ks_709_ = lean_ctor_get(v_x_658_, 0);
v_vs_710_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_730_ == 0)
{
v___x_712_ = v_x_658_;
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_vs_710_);
lean_inc(v_ks_709_);
lean_dec(v_x_658_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_ks_709_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_vs_710_);
v___x_715_ = v_reuseFailAlloc_729_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v_newNode_716_; uint8_t v___y_718_; size_t v___x_724_; uint8_t v___x_725_; 
v_newNode_716_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_715_, v_x_661_, v_x_662_);
v___x_724_ = ((size_t)7ULL);
v___x_725_ = lean_usize_dec_le(v___x_724_, v_x_660_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_716_);
v___x_727_ = lean_unsigned_to_nat(4u);
v___x_728_ = lean_nat_dec_lt(v___x_726_, v___x_727_);
lean_dec(v___x_726_);
v___y_718_ = v___x_728_;
goto v___jp_717_;
}
else
{
v___y_718_ = v___x_725_;
goto v___jp_717_;
}
v___jp_717_:
{
if (v___y_718_ == 0)
{
lean_object* v_ks_719_; lean_object* v_vs_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_ks_719_ = lean_ctor_get(v_newNode_716_, 0);
lean_inc_ref(v_ks_719_);
v_vs_720_ = lean_ctor_get(v_newNode_716_, 1);
lean_inc_ref(v_vs_720_);
lean_dec_ref(v_newNode_716_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_723_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_660_, v_ks_719_, v_vs_720_, v___x_721_, v___x_722_);
lean_dec_ref(v_vs_720_);
lean_dec_ref(v_ks_719_);
return v___x_723_;
}
else
{
return v_newNode_716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_731_, lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_i_734_, lean_object* v_entries_735_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_keys_732_);
v___x_737_ = lean_nat_dec_lt(v_i_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_i_734_);
return v_entries_735_;
}
else
{
lean_object* v_k_738_; lean_object* v_v_739_; uint64_t v___x_740_; size_t v_h_741_; size_t v___x_742_; lean_object* v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v_h_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_k_738_ = lean_array_fget_borrowed(v_keys_732_, v_i_734_);
v_v_739_ = lean_array_fget_borrowed(v_vals_733_, v_i_734_);
v___x_740_ = l_Lean_instHashableExtraModUse_hash(v_k_738_);
v_h_741_ = lean_uint64_to_usize(v___x_740_);
v___x_742_ = ((size_t)5ULL);
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_sub(v_depth_731_, v___x_744_);
v___x_746_ = lean_usize_mul(v___x_742_, v___x_745_);
v_h_747_ = lean_usize_shift_right(v_h_741_, v___x_746_);
v___x_748_ = lean_nat_add(v_i_734_, v___x_743_);
lean_dec(v_i_734_);
lean_inc(v_v_739_);
lean_inc(v_k_738_);
v___x_749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_735_, v_h_747_, v_depth_731_, v_k_738_, v_v_739_);
v_i_734_ = v___x_748_;
v_entries_735_ = v___x_749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_751_, lean_object* v_keys_752_, lean_object* v_vals_753_, lean_object* v_i_754_, lean_object* v_entries_755_){
_start:
{
size_t v_depth_boxed_756_; lean_object* v_res_757_; 
v_depth_boxed_756_ = lean_unbox_usize(v_depth_751_);
lean_dec(v_depth_751_);
v_res_757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_756_, v_keys_752_, v_vals_753_, v_i_754_, v_entries_755_);
lean_dec_ref(v_vals_753_);
lean_dec_ref(v_keys_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
size_t v_x_567__boxed_763_; size_t v_x_568__boxed_764_; lean_object* v_res_765_; 
v_x_567__boxed_763_ = lean_unbox_usize(v_x_759_);
lean_dec(v_x_759_);
v_x_568__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_res_765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_758_, v_x_567__boxed_763_, v_x_568__boxed_764_, v_x_761_, v_x_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint64_t v___x_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_769_ = l_Lean_instHashableExtraModUse_hash(v_x_767_);
v___x_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = ((size_t)1ULL);
v___x_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_766_, v___x_770_, v___x_771_, v_x_767_, v_x_768_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_773_, lean_object* v_k_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(0);
v___x_776_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_773_, v_k_774_, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_777_, lean_object* v_i_778_, lean_object* v_k_779_){
_start:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_array_get_size(v_keys_777_);
v___x_781_ = lean_nat_dec_lt(v_i_778_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v_i_778_);
return v___x_781_;
}
else
{
lean_object* v_k_x27_782_; uint8_t v___x_783_; 
v_k_x27_782_ = lean_array_fget_borrowed(v_keys_777_, v_i_778_);
v___x_783_ = l_Lean_instBEqExtraModUse_beq(v_k_779_, v_k_x27_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_i_778_, v___x_784_);
lean_dec(v_i_778_);
v_i_778_ = v___x_785_;
goto _start;
}
else
{
lean_dec(v_i_778_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_787_, lean_object* v_i_788_, lean_object* v_k_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_787_, v_i_788_, v_k_789_);
lean_dec_ref(v_k_789_);
lean_dec_ref(v_keys_787_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_792_, size_t v_x_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v_es_795_; lean_object* v___x_796_; size_t v___x_797_; size_t v___x_798_; lean_object* v_j_799_; lean_object* v___x_800_; 
v_es_795_ = lean_ctor_get(v_x_792_, 0);
v___x_796_ = lean_box(2);
v___x_797_ = ((size_t)31ULL);
v___x_798_ = lean_usize_land(v_x_793_, v___x_797_);
v_j_799_ = lean_usize_to_nat(v___x_798_);
v___x_800_ = lean_array_get_borrowed(v___x_796_, v_es_795_, v_j_799_);
lean_dec(v_j_799_);
switch(lean_obj_tag(v___x_800_))
{
case 0:
{
lean_object* v_key_801_; uint8_t v___x_802_; 
v_key_801_ = lean_ctor_get(v___x_800_, 0);
v___x_802_ = l_Lean_instBEqExtraModUse_beq(v_x_794_, v_key_801_);
return v___x_802_;
}
case 1:
{
lean_object* v_node_803_; size_t v___x_804_; size_t v___x_805_; 
v_node_803_ = lean_ctor_get(v___x_800_, 0);
v___x_804_ = ((size_t)5ULL);
v___x_805_ = lean_usize_shift_right(v_x_793_, v___x_804_);
v_x_792_ = v_node_803_;
v_x_793_ = v___x_805_;
goto _start;
}
default: 
{
uint8_t v___x_807_; 
v___x_807_ = 0;
return v___x_807_;
}
}
}
else
{
lean_object* v_ks_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_ks_808_ = lean_ctor_get(v_x_792_, 0);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_808_, v___x_809_, v_x_794_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v_x_753__boxed_814_; uint8_t v_res_815_; lean_object* v_r_816_; 
v_x_753__boxed_814_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_815_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_811_, v_x_753__boxed_814_, v_x_813_);
lean_dec_ref(v_x_813_);
lean_dec_ref(v_x_811_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint64_t v___x_819_; size_t v___x_820_; uint8_t v___x_821_; 
v___x_819_ = l_Lean_instHashableExtraModUse_hash(v_x_818_);
v___x_820_ = lean_uint64_to_usize(v___x_819_);
v___x_821_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_817_, v___x_820_, v_x_818_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_822_, v_x_823_);
lean_dec_ref(v_x_823_);
lean_dec_ref(v_x_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_868_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_875_, v_x_876_, v_x_877_);
lean_dec_ref(v_x_877_);
lean_dec_ref(v_x_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, size_t v_x_887_, lean_object* v_x_888_){
_start:
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_886_, v_x_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
size_t v_x_951__boxed_894_; uint8_t v_res_895_; lean_object* v_r_896_; 
v_x_951__boxed_894_ = lean_unbox_usize(v_x_892_);
lean_dec(v_x_892_);
v_res_895_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_890_, v_x_891_, v_x_951__boxed_894_, v_x_893_);
lean_dec_ref(v_x_893_);
lean_dec_ref(v_x_891_);
v_r_896_ = lean_box(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, size_t v_x_899_, size_t v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_898_, v_x_899_, v_x_900_, v_x_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
size_t v_x_962__boxed_910_; size_t v_x_963__boxed_911_; lean_object* v_res_912_; 
v_x_962__boxed_910_ = lean_unbox_usize(v_x_906_);
lean_dec(v_x_906_);
v_x_963__boxed_911_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_res_912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_904_, v_x_905_, v_x_962__boxed_910_, v_x_963__boxed_911_, v_x_908_, v_x_909_);
return v_res_912_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_913_, lean_object* v_keys_914_, lean_object* v_vals_915_, lean_object* v_heq_916_, lean_object* v_i_917_, lean_object* v_k_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_914_, v_i_917_, v_k_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_920_, lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_heq_923_, lean_object* v_i_924_, lean_object* v_k_925_){
_start:
{
uint8_t v_res_926_; lean_object* v_r_927_; 
v_res_926_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_920_, v_keys_921_, v_vals_922_, v_heq_923_, v_i_924_, v_k_925_);
lean_dec_ref(v_k_925_);
lean_dec_ref(v_vals_922_);
lean_dec_ref(v_keys_921_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_928_, lean_object* v_n_929_, lean_object* v_k_930_, lean_object* v_v_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_929_, v_k_930_, v_v_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_933_, size_t v_depth_934_, lean_object* v_keys_935_, lean_object* v_vals_936_, lean_object* v_heq_937_, lean_object* v_i_938_, lean_object* v_entries_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_934_, v_keys_935_, v_vals_936_, v_i_938_, v_entries_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_941_, lean_object* v_depth_942_, lean_object* v_keys_943_, lean_object* v_vals_944_, lean_object* v_heq_945_, lean_object* v_i_946_, lean_object* v_entries_947_){
_start:
{
size_t v_depth_boxed_948_; lean_object* v_res_949_; 
v_depth_boxed_948_ = lean_unbox_usize(v_depth_942_);
lean_dec(v_depth_942_);
v_res_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_941_, v_depth_boxed_948_, v_keys_943_, v_vals_944_, v_heq_945_, v_i_946_, v_entries_947_);
lean_dec_ref(v_vals_944_);
lean_dec_ref(v_keys_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_951_, v_x_952_, v_x_953_, v_x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_957_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_958_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_957_, v___x_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_962_, lean_object* v_modIdx_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; 
v___x_964_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_965_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_966_ = 0;
v___x_967_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_964_, v___x_965_, v_env_962_, v_modIdx_963_, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_968_, lean_object* v_modIdx_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_getExtraModUses(v_env_968_, v_modIdx_969_);
lean_dec(v_modIdx_969_);
lean_dec_ref(v_env_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_971_, lean_object* v_b_972_){
_start:
{
if (lean_obj_tag(v_as_x27_971_) == 0)
{
return v_b_972_;
}
else
{
lean_object* v_head_973_; lean_object* v_tail_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; uint8_t v___x_981_; 
v_head_973_ = lean_ctor_get(v_as_x27_971_, 0);
v_tail_974_ = lean_ctor_get(v_as_x27_971_, 1);
v___x_975_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_976_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_977_ = lean_box(1);
v___x_978_ = lean_box(0);
lean_inc_ref(v_b_972_);
v___x_979_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_975_, v___x_976_, v_b_972_, v___x_977_, v___x_978_);
v___x_980_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_979_, v_head_973_);
lean_dec(v___x_979_);
v___x_981_ = lean_bool_not(v___x_980_);
if (v___x_981_ == 0)
{
v_as_x27_971_ = v_tail_974_;
goto _start;
}
else
{
lean_object* v_toEnvExtension_983_; lean_object* v_asyncMode_984_; lean_object* v___x_985_; 
v_toEnvExtension_983_ = lean_ctor_get(v___x_976_, 0);
v_asyncMode_984_ = lean_ctor_get(v_toEnvExtension_983_, 2);
lean_inc(v_head_973_);
v___x_985_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_976_, v_b_972_, v_head_973_, v_asyncMode_984_, v___x_978_);
v_as_x27_971_ = v_tail_974_;
v_b_972_ = v___x_985_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_987_, lean_object* v_b_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_987_, v_b_988_);
lean_dec(v_as_x27_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_990_, lean_object* v_dest_991_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_992_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_993_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_994_ = lean_box(1);
v___x_995_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_992_, v___x_993_, v_src_990_, v___x_994_);
v___x_996_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_995_, v_dest_991_);
lean_dec(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_997_, lean_object* v_as_x27_998_, lean_object* v_b_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_998_, v_b_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_1002_, lean_object* v_as_x27_1003_, lean_object* v_b_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_1002_, v_as_x27_1003_, v_b_1004_, v_a_1005_);
lean_dec(v_as_x27_1003_);
lean_dec(v_as_1002_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1007_, lean_object* v_entry_1008_, lean_object* v___x_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_toEnvExtension_1011_; lean_object* v_asyncMode_1012_; lean_object* v___x_1013_; 
v_toEnvExtension_1011_ = lean_ctor_get(v___x_1007_, 0);
v_asyncMode_1012_ = lean_ctor_get(v_toEnvExtension_1011_, 2);
lean_inc(v_asyncMode_1012_);
v___x_1013_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1007_, v_x_1010_, v_entry_1008_, v_asyncMode_1012_, v___x_1009_);
lean_dec(v_asyncMode_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_modifyEnv_1033_, lean_object* v___f_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_cls_1039_, lean_object* v_toBind_1040_, lean_object* v___f_1041_, lean_object* v_mod_1042_, lean_object* v_hint_1043_, uint8_t v_isMeta_1044_, uint8_t v_isExporting_1045_, uint8_t v_____do__lift_1046_){
_start:
{
lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1054_; lean_object* v___y_1055_; 
if (v_____do__lift_1046_ == 0)
{
lean_object* v___x_1067_; 
lean_dec(v_hint_1043_);
lean_dec(v_mod_1042_);
lean_dec(v___f_1041_);
lean_dec(v_toBind_1040_);
lean_dec(v_cls_1039_);
lean_dec(v_inst_1038_);
lean_dec_ref(v_inst_1037_);
lean_dec_ref(v_inst_1036_);
lean_dec_ref(v_inst_1035_);
v___x_1067_ = lean_apply_1(v_modifyEnv_1033_, v___f_1034_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; lean_object* v___y_1070_; 
lean_dec_ref(v___f_1034_);
lean_dec(v_modifyEnv_1033_);
v___x_1068_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
if (v_isExporting_1045_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12));
v___y_1070_ = v___x_1077_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13));
v___y_1070_ = v___x_1078_;
goto v___jp_1069_;
}
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_inc_ref(v___y_1070_);
v___x_1071_ = l_Lean_stringToMessageData(v___y_1070_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1068_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
if (v_isMeta_1044_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10));
v___y_1054_ = v___x_1074_;
v___y_1055_ = v___x_1075_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11));
v___y_1054_ = v___x_1074_;
v___y_1055_ = v___x_1076_;
goto v___jp_1053_;
}
}
}
v___jp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___y_1048_);
lean_ctor_set(v___x_1050_, 1, v___y_1049_);
v___x_1051_ = l_Lean_addTrace___redArg(v_inst_1035_, v_inst_1036_, v_inst_1037_, v_inst_1038_, v_cls_1039_, v___x_1050_);
v___x_1052_ = lean_apply_4(v_toBind_1040_, lean_box(0), lean_box(0), v___x_1051_, v___f_1041_);
return v___x_1052_;
}
v___jp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
lean_inc_ref(v___y_1055_);
v___x_1056_ = l_Lean_stringToMessageData(v___y_1055_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___y_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_MessageData_ofName(v_mod_1042_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_Name_isAnonymous(v_hint_1043_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
v___x_1064_ = l_Lean_MessageData_ofName(v_hint_1043_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___y_1048_ = v___x_1061_;
v___y_1049_ = v___x_1065_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_hint_1043_);
v___x_1066_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
v___y_1048_ = v___x_1061_;
v___y_1049_ = v___x_1066_;
goto v___jp_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_modifyEnv_1079_, lean_object* v___f_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_cls_1085_, lean_object* v_toBind_1086_, lean_object* v___f_1087_, lean_object* v_mod_1088_, lean_object* v_hint_1089_, lean_object* v_isMeta_1090_, lean_object* v_isExporting_1091_, lean_object* v_____do__lift_1092_){
_start:
{
uint8_t v_isMeta_boxed_1093_; uint8_t v_isExporting_boxed_1094_; uint8_t v_____do__lift_766__boxed_1095_; lean_object* v_res_1096_; 
v_isMeta_boxed_1093_ = lean_unbox(v_isMeta_1090_);
v_isExporting_boxed_1094_ = lean_unbox(v_isExporting_1091_);
v_____do__lift_766__boxed_1095_ = lean_unbox(v_____do__lift_1092_);
v_res_1096_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_modifyEnv_1079_, v___f_1080_, v_inst_1081_, v_inst_1082_, v_inst_1083_, v_inst_1084_, v_cls_1085_, v_toBind_1086_, v___f_1087_, v_mod_1088_, v_hint_1089_, v_isMeta_boxed_1093_, v_isExporting_boxed_1094_, v_____do__lift_766__boxed_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_entry_1100_, lean_object* v_toApplicative_1101_, lean_object* v_inst_1102_, lean_object* v_modifyEnv_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_toBind_1107_, lean_object* v_mod_1108_, lean_object* v_hint_1109_, uint8_t v_isMeta_1110_, uint8_t v_isExporting_1111_, lean_object* v_inst_1112_, lean_object* v_____do__lift_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1114_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1115_ = lean_box(1);
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1097_, v___x_1114_, v_____do__lift_1113_, v___x_1115_, v___x_1116_);
lean_inc_ref(v_entry_1100_);
v___x_1118_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1098_, v___x_1099_, v___x_1117_, v_entry_1100_);
v___x_1119_ = lean_bool_not(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v_toPure_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_inst_1112_);
lean_dec(v_hint_1109_);
lean_dec(v_mod_1108_);
lean_dec(v_toBind_1107_);
lean_dec(v_inst_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_inst_1104_);
lean_dec(v_modifyEnv_1103_);
lean_dec_ref(v_inst_1102_);
lean_dec_ref(v_entry_1100_);
v_toPure_1120_ = lean_ctor_get(v_toApplicative_1101_, 1);
lean_inc(v_toPure_1120_);
lean_dec_ref(v_toApplicative_1101_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_apply_2(v_toPure_1120_, lean_box(0), v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v_getInheritedTraceOptions_1123_; lean_object* v_toPure_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v_cls_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_getInheritedTraceOptions_1123_ = lean_ctor_get(v_inst_1102_, 2);
lean_inc(v_getInheritedTraceOptions_1123_);
v_toPure_1124_ = lean_ctor_get(v_toApplicative_1101_, 1);
lean_inc(v_toPure_1124_);
lean_dec_ref(v_toApplicative_1101_);
v___f_1125_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1125_, 0, v___x_1114_);
lean_closure_set(v___f_1125_, 1, v_entry_1100_);
lean_closure_set(v___f_1125_, 2, v___x_1116_);
lean_inc_ref(v___f_1125_);
lean_inc(v_modifyEnv_1103_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1126_, 0, v_modifyEnv_1103_);
lean_closure_set(v___f_1126_, 1, v___f_1125_);
v_cls_1127_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1128_ = lean_box(v_isMeta_1110_);
v___x_1129_ = lean_box(v_isExporting_1111_);
lean_inc_n(v_toBind_1107_, 3);
v___f_1130_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1130_, 0, v_modifyEnv_1103_);
lean_closure_set(v___f_1130_, 1, v___f_1125_);
lean_closure_set(v___f_1130_, 2, v_inst_1104_);
lean_closure_set(v___f_1130_, 3, v_inst_1102_);
lean_closure_set(v___f_1130_, 4, v_inst_1105_);
lean_closure_set(v___f_1130_, 5, v_inst_1106_);
lean_closure_set(v___f_1130_, 6, v_cls_1127_);
lean_closure_set(v___f_1130_, 7, v_toBind_1107_);
lean_closure_set(v___f_1130_, 8, v___f_1126_);
lean_closure_set(v___f_1130_, 9, v_mod_1108_);
lean_closure_set(v___f_1130_, 10, v_hint_1109_);
lean_closure_set(v___f_1130_, 11, v___x_1128_);
lean_closure_set(v___f_1130_, 12, v___x_1129_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1131_, 0, v_toPure_1124_);
lean_closure_set(v___f_1131_, 1, v_cls_1127_);
lean_closure_set(v___f_1131_, 2, v_toBind_1107_);
lean_closure_set(v___f_1131_, 3, v_inst_1112_);
v___x_1132_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1123_, v___f_1131_);
v___x_1133_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v___x_1132_, v___f_1130_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1134_ = _args[0];
lean_object* v___x_1135_ = _args[1];
lean_object* v___x_1136_ = _args[2];
lean_object* v_entry_1137_ = _args[3];
lean_object* v_toApplicative_1138_ = _args[4];
lean_object* v_inst_1139_ = _args[5];
lean_object* v_modifyEnv_1140_ = _args[6];
lean_object* v_inst_1141_ = _args[7];
lean_object* v_inst_1142_ = _args[8];
lean_object* v_inst_1143_ = _args[9];
lean_object* v_toBind_1144_ = _args[10];
lean_object* v_mod_1145_ = _args[11];
lean_object* v_hint_1146_ = _args[12];
lean_object* v_isMeta_1147_ = _args[13];
lean_object* v_isExporting_1148_ = _args[14];
lean_object* v_inst_1149_ = _args[15];
lean_object* v_____do__lift_1150_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1151_; uint8_t v_isExporting_boxed_1152_; lean_object* v_res_1153_; 
v_isMeta_boxed_1151_ = lean_unbox(v_isMeta_1147_);
v_isExporting_boxed_1152_ = lean_unbox(v_isExporting_1148_);
v_res_1153_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v___x_1134_, v___x_1135_, v___x_1136_, v_entry_1137_, v_toApplicative_1138_, v_inst_1139_, v_modifyEnv_1140_, v_inst_1141_, v_inst_1142_, v_inst_1143_, v_toBind_1144_, v_mod_1145_, v_hint_1146_, v_isMeta_boxed_1151_, v_isExporting_boxed_1152_, v_inst_1149_, v_____do__lift_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v_mod_1154_, uint8_t v_isMeta_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v_toApplicative_1159_, lean_object* v_inst_1160_, lean_object* v_modifyEnv_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_toBind_1165_, lean_object* v_hint_1166_, lean_object* v_inst_1167_, lean_object* v_getEnv_1168_, lean_object* v_____do__lift_1169_){
_start:
{
uint8_t v_isExporting_1170_; lean_object* v_entry_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v_isExporting_1170_ = lean_ctor_get_uint8(v_____do__lift_1169_, sizeof(void*)*8);
lean_inc(v_mod_1154_);
v_entry_1171_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1171_, 0, v_mod_1154_);
lean_ctor_set_uint8(v_entry_1171_, sizeof(void*)*1, v_isExporting_1170_);
lean_ctor_set_uint8(v_entry_1171_, sizeof(void*)*1 + 1, v_isMeta_1155_);
v___x_1172_ = lean_box(v_isMeta_1155_);
v___x_1173_ = lean_box(v_isExporting_1170_);
lean_inc(v_toBind_1165_);
v___f_1174_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1174_, 0, v___x_1156_);
lean_closure_set(v___f_1174_, 1, v___x_1157_);
lean_closure_set(v___f_1174_, 2, v___x_1158_);
lean_closure_set(v___f_1174_, 3, v_entry_1171_);
lean_closure_set(v___f_1174_, 4, v_toApplicative_1159_);
lean_closure_set(v___f_1174_, 5, v_inst_1160_);
lean_closure_set(v___f_1174_, 6, v_modifyEnv_1161_);
lean_closure_set(v___f_1174_, 7, v_inst_1162_);
lean_closure_set(v___f_1174_, 8, v_inst_1163_);
lean_closure_set(v___f_1174_, 9, v_inst_1164_);
lean_closure_set(v___f_1174_, 10, v_toBind_1165_);
lean_closure_set(v___f_1174_, 11, v_mod_1154_);
lean_closure_set(v___f_1174_, 12, v_hint_1166_);
lean_closure_set(v___f_1174_, 13, v___x_1172_);
lean_closure_set(v___f_1174_, 14, v___x_1173_);
lean_closure_set(v___f_1174_, 15, v_inst_1167_);
v___x_1175_ = lean_apply_4(v_toBind_1165_, lean_box(0), lean_box(0), v_getEnv_1168_, v___f_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object* v_mod_1176_, lean_object* v_isMeta_1177_, lean_object* v___x_1178_, lean_object* v___x_1179_, lean_object* v___x_1180_, lean_object* v_toApplicative_1181_, lean_object* v_inst_1182_, lean_object* v_modifyEnv_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_toBind_1187_, lean_object* v_hint_1188_, lean_object* v_inst_1189_, lean_object* v_getEnv_1190_, lean_object* v_____do__lift_1191_){
_start:
{
uint8_t v_isMeta_boxed_1192_; lean_object* v_res_1193_; 
v_isMeta_boxed_1192_ = lean_unbox(v_isMeta_1177_);
v_res_1193_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v_mod_1176_, v_isMeta_boxed_1192_, v___x_1178_, v___x_1179_, v___x_1180_, v_toApplicative_1181_, v_inst_1182_, v_modifyEnv_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_, v_toBind_1187_, v_hint_1188_, v_inst_1189_, v_getEnv_1190_, v_____do__lift_1191_);
lean_dec_ref(v_____do__lift_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_mod_1200_, uint8_t v_isMeta_1201_, lean_object* v_hint_1202_){
_start:
{
lean_object* v_toApplicative_1203_; lean_object* v_toBind_1204_; lean_object* v_getEnv_1205_; lean_object* v_modifyEnv_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; 
v_toApplicative_1203_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc_ref(v_toApplicative_1203_);
v_toBind_1204_ = lean_ctor_get(v_inst_1194_, 1);
lean_inc_n(v_toBind_1204_, 2);
v_getEnv_1205_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc_n(v_getEnv_1205_, 2);
v_modifyEnv_1206_ = lean_ctor_get(v_inst_1195_, 1);
lean_inc(v_modifyEnv_1206_);
lean_dec_ref(v_inst_1195_);
v___x_1207_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1208_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1209_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1210_ = lean_box(v_isMeta_1201_);
v___f_1211_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 16, 15);
lean_closure_set(v___f_1211_, 0, v_mod_1200_);
lean_closure_set(v___f_1211_, 1, v___x_1210_);
lean_closure_set(v___f_1211_, 2, v___x_1209_);
lean_closure_set(v___f_1211_, 3, v___x_1207_);
lean_closure_set(v___f_1211_, 4, v___x_1208_);
lean_closure_set(v___f_1211_, 5, v_toApplicative_1203_);
lean_closure_set(v___f_1211_, 6, v_inst_1196_);
lean_closure_set(v___f_1211_, 7, v_modifyEnv_1206_);
lean_closure_set(v___f_1211_, 8, v_inst_1194_);
lean_closure_set(v___f_1211_, 9, v_inst_1198_);
lean_closure_set(v___f_1211_, 10, v_inst_1199_);
lean_closure_set(v___f_1211_, 11, v_toBind_1204_);
lean_closure_set(v___f_1211_, 12, v_hint_1202_);
lean_closure_set(v___f_1211_, 13, v_inst_1197_);
lean_closure_set(v___f_1211_, 14, v_getEnv_1205_);
v___x_1212_ = lean_apply_4(v_toBind_1204_, lean_box(0), lean_box(0), v_getEnv_1205_, v___f_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_mod_1219_, lean_object* v_isMeta_1220_, lean_object* v_hint_1221_){
_start:
{
uint8_t v_isMeta_boxed_1222_; lean_object* v_res_1223_; 
v_isMeta_boxed_1222_ = lean_unbox(v_isMeta_1220_);
v_res_1223_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1213_, v_inst_1214_, v_inst_1215_, v_inst_1216_, v_inst_1217_, v_inst_1218_, v_mod_1219_, v_isMeta_boxed_1222_, v_hint_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_mod_1231_, uint8_t v_isMeta_1232_, lean_object* v_hint_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1225_, v_inst_1226_, v_inst_1227_, v_inst_1228_, v_inst_1229_, v_inst_1230_, v_mod_1231_, v_isMeta_1232_, v_hint_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_mod_1242_, lean_object* v_isMeta_1243_, lean_object* v_hint_1244_){
_start:
{
uint8_t v_isMeta_boxed_1245_; lean_object* v_res_1246_; 
v_isMeta_boxed_1245_ = lean_unbox(v_isMeta_1243_);
v_res_1246_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1235_, v_inst_1236_, v_inst_1237_, v_inst_1238_, v_inst_1239_, v_inst_1240_, v_inst_1241_, v_mod_1242_, v_isMeta_boxed_1245_, v_hint_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1247_, lean_object* v_toApplicative_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, uint8_t v_isMeta_1255_, lean_object* v_____do__lift_1256_){
_start:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = l_Lean_Environment_mainModule(v_____do__lift_1256_);
v___x_1258_ = lean_name_eq(v_modName_1247_, v___x_1257_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_bool_not(v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v_toPure_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_inst_1254_);
lean_dec_ref(v_inst_1253_);
lean_dec(v_inst_1252_);
lean_dec_ref(v_inst_1251_);
lean_dec_ref(v_inst_1250_);
lean_dec_ref(v_inst_1249_);
lean_dec(v_modName_1247_);
v_toPure_1260_ = lean_ctor_get(v_toApplicative_1248_, 1);
lean_inc(v_toPure_1260_);
lean_dec_ref(v_toApplicative_1248_);
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_apply_2(v_toPure_1260_, lean_box(0), v___x_1261_);
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v_toApplicative_1248_);
v___x_1263_ = lean_box(0);
v___x_1264_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1249_, v_inst_1250_, v_inst_1251_, v_inst_1252_, v_inst_1253_, v_inst_1254_, v_modName_1247_, v_isMeta_1255_, v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1265_, lean_object* v_toApplicative_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_isMeta_1273_, lean_object* v_____do__lift_1274_){
_start:
{
uint8_t v_isMeta_boxed_1275_; lean_object* v_res_1276_; 
v_isMeta_boxed_1275_ = lean_unbox(v_isMeta_1273_);
v_res_1276_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1265_, v_toApplicative_1266_, v_inst_1267_, v_inst_1268_, v_inst_1269_, v_inst_1270_, v_inst_1271_, v_inst_1272_, v_isMeta_boxed_1275_, v_____do__lift_1274_);
lean_dec_ref(v_____do__lift_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_modName_1283_, uint8_t v_isMeta_1284_){
_start:
{
lean_object* v_toApplicative_1285_; lean_object* v_toBind_1286_; lean_object* v_getEnv_1287_; lean_object* v___x_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; 
v_toApplicative_1285_ = lean_ctor_get(v_inst_1277_, 0);
lean_inc_ref(v_toApplicative_1285_);
v_toBind_1286_ = lean_ctor_get(v_inst_1277_, 1);
lean_inc(v_toBind_1286_);
v_getEnv_1287_ = lean_ctor_get(v_inst_1278_, 0);
lean_inc(v_getEnv_1287_);
v___x_1288_ = lean_box(v_isMeta_1284_);
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1289_, 0, v_modName_1283_);
lean_closure_set(v___f_1289_, 1, v_toApplicative_1285_);
lean_closure_set(v___f_1289_, 2, v_inst_1277_);
lean_closure_set(v___f_1289_, 3, v_inst_1278_);
lean_closure_set(v___f_1289_, 4, v_inst_1279_);
lean_closure_set(v___f_1289_, 5, v_inst_1280_);
lean_closure_set(v___f_1289_, 6, v_inst_1281_);
lean_closure_set(v___f_1289_, 7, v_inst_1282_);
lean_closure_set(v___f_1289_, 8, v___x_1288_);
v___x_1290_ = lean_apply_4(v_toBind_1286_, lean_box(0), lean_box(0), v_getEnv_1287_, v___f_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_modName_1297_, lean_object* v_isMeta_1298_){
_start:
{
uint8_t v_isMeta_boxed_1299_; lean_object* v_res_1300_; 
v_isMeta_boxed_1299_ = lean_unbox(v_isMeta_1298_);
v_res_1300_ = l_Lean_recordExtraModUse___redArg(v_inst_1291_, v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_modName_1297_, v_isMeta_boxed_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_modName_1308_, uint8_t v_isMeta_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_recordExtraModUse___redArg(v_inst_1302_, v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_, v_modName_1308_, v_isMeta_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_modName_1318_, lean_object* v_isMeta_1319_){
_start:
{
uint8_t v_isMeta_boxed_1320_; lean_object* v_res_1321_; 
v_isMeta_boxed_1320_ = lean_unbox(v_isMeta_1319_);
v_res_1321_ = l_Lean_recordExtraModUse(v_m_1311_, v_inst_1312_, v_inst_1313_, v_inst_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_modName_1318_, v_isMeta_boxed_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1322_, lean_object* v_____s_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_apply_2(v_toPure_1322_, lean_box(0), v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1326_, lean_object* v_toPure_1327_, lean_object* v_r_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1326_);
v___x_1330_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1331_, lean_object* v___x_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_declName_1339_, lean_object* v_toBind_1340_, lean_object* v___f_1341_, lean_object* v_a_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v_modules_1346_; lean_object* v___x_1347_; lean_object* v_toImport_1348_; lean_object* v_module_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1345_ = l_Lean_Environment_header(v_env_1331_);
v_modules_1346_ = lean_ctor_get(v___x_1345_, 3);
lean_inc_ref(v_modules_1346_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = lean_array_get(v___x_1332_, v_modules_1346_, v_a_1342_);
lean_dec_ref(v_modules_1346_);
v_toImport_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_toImport_1348_);
lean_dec(v___x_1347_);
v_module_1349_ = lean_ctor_get(v_toImport_1348_, 0);
lean_inc(v_module_1349_);
lean_dec_ref(v_toImport_1348_);
v___x_1350_ = 0;
v___x_1351_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1333_, v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_module_1349_, v___x_1350_, v_declName_1339_);
v___x_1352_ = lean_apply_4(v_toBind_1340_, lean_box(0), lean_box(0), v___x_1351_, v___f_1341_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1353_, lean_object* v___x_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_declName_1361_, lean_object* v_toBind_1362_, lean_object* v___f_1363_, lean_object* v_a_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1353_, v___x_1354_, v_inst_1355_, v_inst_1356_, v_inst_1357_, v_inst_1358_, v_inst_1359_, v_inst_1360_, v_declName_1361_, v_toBind_1362_, v___f_1363_, v_a_1364_, v_x_1365_, v___y_1366_);
lean_dec(v_a_1364_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v_env_1353_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1368_, lean_object* v_env_1369_, lean_object* v___x_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_declName_1377_, lean_object* v_toBind_1378_, lean_object* v___f_1379_, lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v_____r_1383_){
_start:
{
lean_object* v___y_1385_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1393_ = l_Lean_indirectModUseExt;
v___x_1394_ = lean_box(1);
v___x_1395_ = lean_box(0);
lean_inc_ref(v_env_1369_);
v___x_1396_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1380_, v___x_1393_, v_env_1369_, v___x_1394_, v___x_1395_);
lean_inc(v_declName_1377_);
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1381_, v___x_1382_, v___x_1396_, v_declName_1377_);
lean_dec(v___x_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1385_ = v___x_1398_;
goto v___jp_1384_;
}
else
{
lean_object* v_val_1399_; 
v_val_1399_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_val_1399_);
lean_dec_ref_known(v___x_1397_, 1);
v___y_1385_ = v_val_1399_;
goto v___jp_1384_;
}
v___jp_1384_:
{
lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1386_ = lean_box(0);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1387_, 0, v___x_1386_);
lean_closure_set(v___f_1387_, 1, v_toPure_1368_);
lean_inc(v_toBind_1378_);
lean_inc_ref(v_inst_1371_);
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1388_, 0, v_env_1369_);
lean_closure_set(v___f_1388_, 1, v___x_1370_);
lean_closure_set(v___f_1388_, 2, v_inst_1371_);
lean_closure_set(v___f_1388_, 3, v_inst_1372_);
lean_closure_set(v___f_1388_, 4, v_inst_1373_);
lean_closure_set(v___f_1388_, 5, v_inst_1374_);
lean_closure_set(v___f_1388_, 6, v_inst_1375_);
lean_closure_set(v___f_1388_, 7, v_inst_1376_);
lean_closure_set(v___f_1388_, 8, v_declName_1377_);
lean_closure_set(v___f_1388_, 9, v_toBind_1378_);
lean_closure_set(v___f_1388_, 10, v___f_1387_);
v_sz_1389_ = lean_array_size(v___y_1385_);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1371_, v___y_1385_, v___f_1388_, v_sz_1389_, v___x_1390_, v___x_1386_);
v___x_1392_ = lean_apply_4(v_toBind_1378_, lean_box(0), lean_box(0), v___x_1391_, v___f_1379_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_declName_1407_, lean_object* v_toBind_1408_, lean_object* v___f_1409_, uint8_t v_isMeta_1410_, lean_object* v_____do__lift_1411_){
_start:
{
uint8_t v___y_1413_; 
if (v_isMeta_1410_ == 0)
{
lean_dec_ref(v_____do__lift_1411_);
v___y_1413_ = v_isMeta_1410_;
goto v___jp_1412_;
}
else
{
uint8_t v___x_1418_; uint8_t v___x_1419_; 
lean_inc(v_declName_1407_);
v___x_1418_ = l_Lean_isMarkedMeta(v_____do__lift_1411_, v_declName_1407_);
v___x_1419_ = lean_bool_not(v___x_1418_);
v___y_1413_ = v___x_1419_;
goto v___jp_1412_;
}
v___jp_1412_:
{
lean_object* v_toImport_1414_; lean_object* v_module_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_toImport_1414_ = lean_ctor_get(v___x_1400_, 0);
lean_inc_ref(v_toImport_1414_);
lean_dec_ref(v___x_1400_);
v_module_1415_ = lean_ctor_get(v_toImport_1414_, 0);
lean_inc(v_module_1415_);
lean_dec_ref(v_toImport_1414_);
v___x_1416_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1401_, v_inst_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_inst_1406_, v_module_1415_, v___y_1413_, v_declName_1407_);
v___x_1417_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1416_, v___f_1409_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_declName_1427_, lean_object* v_toBind_1428_, lean_object* v___f_1429_, lean_object* v_isMeta_1430_, lean_object* v_____do__lift_1431_){
_start:
{
uint8_t v_isMeta_boxed_1432_; lean_object* v_res_1433_; 
v_isMeta_boxed_1432_ = lean_unbox(v_isMeta_1430_);
v_res_1433_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1420_, v_inst_1421_, v_inst_1422_, v_inst_1423_, v_inst_1424_, v_inst_1425_, v_inst_1426_, v_declName_1427_, v_toBind_1428_, v___f_1429_, v_isMeta_boxed_1432_, v_____do__lift_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1434_, lean_object* v_declName_1435_, lean_object* v___x_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_toBind_1443_, lean_object* v___f_1444_, lean_object* v___x_1445_, lean_object* v___x_1446_, lean_object* v___x_1447_, uint8_t v_isMeta_1448_, lean_object* v_getEnv_1449_, lean_object* v_env_1450_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1450_, v_declName_1435_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_dec_ref(v_env_1450_);
lean_dec(v_getEnv_1449_);
lean_dec_ref(v___x_1447_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1445_);
lean_dec(v___f_1444_);
lean_dec(v_toBind_1443_);
lean_dec(v_inst_1442_);
lean_dec_ref(v_inst_1441_);
lean_dec(v_inst_1440_);
lean_dec_ref(v_inst_1439_);
lean_dec_ref(v_inst_1438_);
lean_dec_ref(v_inst_1437_);
lean_dec_ref(v___x_1436_);
lean_dec(v_declName_1435_);
goto v___jp_1451_;
}
else
{
lean_object* v_val_1455_; lean_object* v___x_1456_; lean_object* v_modules_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = l_Lean_Environment_header(v_env_1450_);
v_modules_1457_ = lean_ctor_get(v___x_1456_, 3);
lean_inc_ref(v_modules_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = lean_array_get_size(v_modules_1457_);
v___x_1459_ = lean_nat_dec_lt(v_val_1455_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_dec_ref(v_modules_1457_);
lean_dec(v_val_1455_);
lean_dec_ref(v_env_1450_);
lean_dec(v_getEnv_1449_);
lean_dec_ref(v___x_1447_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1445_);
lean_dec(v___f_1444_);
lean_dec(v_toBind_1443_);
lean_dec(v_inst_1442_);
lean_dec_ref(v_inst_1441_);
lean_dec(v_inst_1440_);
lean_dec_ref(v_inst_1439_);
lean_dec_ref(v_inst_1438_);
lean_dec_ref(v_inst_1437_);
lean_dec_ref(v___x_1436_);
lean_dec(v_declName_1435_);
goto v___jp_1451_;
}
else
{
lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; 
lean_inc_n(v_toBind_1443_, 2);
lean_inc(v_declName_1435_);
lean_inc(v_inst_1442_);
lean_inc_ref(v_inst_1441_);
lean_inc(v_inst_1440_);
lean_inc_ref(v_inst_1439_);
lean_inc_ref(v_inst_1438_);
lean_inc_ref(v_inst_1437_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1460_, 0, v_toPure_1434_);
lean_closure_set(v___f_1460_, 1, v_env_1450_);
lean_closure_set(v___f_1460_, 2, v___x_1436_);
lean_closure_set(v___f_1460_, 3, v_inst_1437_);
lean_closure_set(v___f_1460_, 4, v_inst_1438_);
lean_closure_set(v___f_1460_, 5, v_inst_1439_);
lean_closure_set(v___f_1460_, 6, v_inst_1440_);
lean_closure_set(v___f_1460_, 7, v_inst_1441_);
lean_closure_set(v___f_1460_, 8, v_inst_1442_);
lean_closure_set(v___f_1460_, 9, v_declName_1435_);
lean_closure_set(v___f_1460_, 10, v_toBind_1443_);
lean_closure_set(v___f_1460_, 11, v___f_1444_);
lean_closure_set(v___f_1460_, 12, v___x_1445_);
lean_closure_set(v___f_1460_, 13, v___x_1446_);
lean_closure_set(v___f_1460_, 14, v___x_1447_);
v___x_1461_ = lean_array_fget(v_modules_1457_, v_val_1455_);
lean_dec(v_val_1455_);
lean_dec_ref(v_modules_1457_);
v___x_1462_ = lean_box(v_isMeta_1448_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1463_, 0, v___x_1461_);
lean_closure_set(v___f_1463_, 1, v_inst_1437_);
lean_closure_set(v___f_1463_, 2, v_inst_1438_);
lean_closure_set(v___f_1463_, 3, v_inst_1439_);
lean_closure_set(v___f_1463_, 4, v_inst_1440_);
lean_closure_set(v___f_1463_, 5, v_inst_1441_);
lean_closure_set(v___f_1463_, 6, v_inst_1442_);
lean_closure_set(v___f_1463_, 7, v_declName_1435_);
lean_closure_set(v___f_1463_, 8, v_toBind_1443_);
lean_closure_set(v___f_1463_, 9, v___f_1460_);
lean_closure_set(v___f_1463_, 10, v___x_1462_);
v___x_1464_ = lean_apply_4(v_toBind_1443_, lean_box(0), lean_box(0), v_getEnv_1449_, v___f_1463_);
return v___x_1464_;
}
}
v___jp_1451_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_apply_2(v_toPure_1434_, lean_box(0), v___x_1452_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1465_ = _args[0];
lean_object* v_declName_1466_ = _args[1];
lean_object* v___x_1467_ = _args[2];
lean_object* v_inst_1468_ = _args[3];
lean_object* v_inst_1469_ = _args[4];
lean_object* v_inst_1470_ = _args[5];
lean_object* v_inst_1471_ = _args[6];
lean_object* v_inst_1472_ = _args[7];
lean_object* v_inst_1473_ = _args[8];
lean_object* v_toBind_1474_ = _args[9];
lean_object* v___f_1475_ = _args[10];
lean_object* v___x_1476_ = _args[11];
lean_object* v___x_1477_ = _args[12];
lean_object* v___x_1478_ = _args[13];
lean_object* v_isMeta_1479_ = _args[14];
lean_object* v_getEnv_1480_ = _args[15];
lean_object* v_env_1481_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1482_; lean_object* v_res_1483_; 
v_isMeta_boxed_1482_ = lean_unbox(v_isMeta_1479_);
v_res_1483_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1465_, v_declName_1466_, v___x_1467_, v_inst_1468_, v_inst_1469_, v_inst_1470_, v_inst_1471_, v_inst_1472_, v_inst_1473_, v_toBind_1474_, v___f_1475_, v___x_1476_, v___x_1477_, v___x_1478_, v_isMeta_boxed_1482_, v_getEnv_1480_, v_env_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_declName_1490_, uint8_t v_isMeta_1491_){
_start:
{
lean_object* v_toApplicative_1492_; lean_object* v_toBind_1493_; lean_object* v_getEnv_1494_; lean_object* v_toPure_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; 
v_toApplicative_1492_ = lean_ctor_get(v_inst_1484_, 0);
v_toBind_1493_ = lean_ctor_get(v_inst_1484_, 1);
lean_inc_n(v_toBind_1493_, 2);
v_getEnv_1494_ = lean_ctor_get(v_inst_1485_, 0);
lean_inc_n(v_getEnv_1494_, 2);
v_toPure_1495_ = lean_ctor_get(v_toApplicative_1492_, 1);
lean_inc_n(v_toPure_1495_, 2);
v___x_1496_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1497_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1498_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1499_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1500_, 0, v_toPure_1495_);
v___x_1501_ = lean_box(v_isMeta_1491_);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1502_, 0, v_toPure_1495_);
lean_closure_set(v___f_1502_, 1, v_declName_1490_);
lean_closure_set(v___f_1502_, 2, v___x_1499_);
lean_closure_set(v___f_1502_, 3, v_inst_1484_);
lean_closure_set(v___f_1502_, 4, v_inst_1485_);
lean_closure_set(v___f_1502_, 5, v_inst_1486_);
lean_closure_set(v___f_1502_, 6, v_inst_1487_);
lean_closure_set(v___f_1502_, 7, v_inst_1488_);
lean_closure_set(v___f_1502_, 8, v_inst_1489_);
lean_closure_set(v___f_1502_, 9, v_toBind_1493_);
lean_closure_set(v___f_1502_, 10, v___f_1500_);
lean_closure_set(v___f_1502_, 11, v___x_1498_);
lean_closure_set(v___f_1502_, 12, v___x_1496_);
lean_closure_set(v___f_1502_, 13, v___x_1497_);
lean_closure_set(v___f_1502_, 14, v___x_1501_);
lean_closure_set(v___f_1502_, 15, v_getEnv_1494_);
v___x_1503_ = lean_apply_4(v_toBind_1493_, lean_box(0), lean_box(0), v_getEnv_1494_, v___f_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_declName_1510_, lean_object* v_isMeta_1511_){
_start:
{
uint8_t v_isMeta_boxed_1512_; lean_object* v_res_1513_; 
v_isMeta_boxed_1512_ = lean_unbox(v_isMeta_1511_);
v_res_1513_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1504_, v_inst_1505_, v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_declName_1510_, v_isMeta_boxed_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_declName_1521_, uint8_t v_isMeta_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1515_, v_inst_1516_, v_inst_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_declName_1521_, v_isMeta_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_declName_1531_, lean_object* v_isMeta_1532_){
_start:
{
uint8_t v_isMeta_boxed_1533_; lean_object* v_res_1534_; 
v_isMeta_boxed_1533_ = lean_unbox(v_isMeta_1532_);
v_res_1534_ = l_Lean_recordExtraModUseFromDecl(v_m_1524_, v_inst_1525_, v_inst_1526_, v_inst_1527_, v_inst_1528_, v_inst_1529_, v_inst_1530_, v_declName_1531_, v_isMeta_boxed_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1535_, lean_object* v_e_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1540_);
lean_dec_ref(v_x_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_array_mk(v_es_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1560_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1562_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1566_, lean_object* v_modIdx_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; uint8_t v___x_1575_; 
v___x_1568_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1569_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1570_ = 0;
v___x_1571_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1568_, v___x_1569_, v_env_1566_, v_modIdx_1567_, v___x_1570_);
v___x_1572_ = lean_array_get_size(v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_nat_dec_eq(v___x_1572_, v___x_1573_);
v___x_1575_ = lean_bool_not(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1576_, lean_object* v_modIdx_1577_){
_start:
{
uint8_t v_res_1578_; lean_object* v_r_1579_; 
v_res_1578_ = l_Lean_isExtraRevModUse(v_env_1576_, v_modIdx_1577_);
lean_dec(v_modIdx_1577_);
lean_dec_ref(v_env_1576_);
v_r_1579_ = lean_box(v_res_1578_);
return v_r_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v_toEnvExtension_1582_; lean_object* v_asyncMode_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_toEnvExtension_1582_ = lean_ctor_get(v___x_1580_, 0);
v_asyncMode_1583_ = lean_ctor_get(v_toEnvExtension_1582_, 2);
lean_inc(v_asyncMode_1583_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_box(0);
v___x_1586_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1580_, v_x_1581_, v___x_1584_, v_asyncMode_1583_, v___x_1585_);
lean_dec(v_asyncMode_1583_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v_modifyEnv_1590_, lean_object* v___f_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_cls_1596_, lean_object* v_toBind_1597_, lean_object* v___f_1598_, uint8_t v_____do__lift_1599_){
_start:
{
if (v_____do__lift_1599_ == 0)
{
lean_object* v___x_1600_; 
lean_dec(v___f_1598_);
lean_dec(v_toBind_1597_);
lean_dec(v_cls_1596_);
lean_dec(v_inst_1595_);
lean_dec_ref(v_inst_1594_);
lean_dec_ref(v_inst_1593_);
lean_dec_ref(v_inst_1592_);
v___x_1600_ = lean_apply_1(v_modifyEnv_1590_, v___f_1591_);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v___f_1591_);
lean_dec(v_modifyEnv_1590_);
v___x_1601_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1);
v___x_1602_ = l_Lean_addTrace___redArg(v_inst_1592_, v_inst_1593_, v_inst_1594_, v_inst_1595_, v_cls_1596_, v___x_1601_);
v___x_1603_ = lean_apply_4(v_toBind_1597_, lean_box(0), lean_box(0), v___x_1602_, v___f_1598_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object* v_modifyEnv_1604_, lean_object* v___f_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_cls_1610_, lean_object* v_toBind_1611_, lean_object* v___f_1612_, lean_object* v_____do__lift_1613_){
_start:
{
uint8_t v_____do__lift_328__boxed_1614_; lean_object* v_res_1615_; 
v_____do__lift_328__boxed_1614_ = lean_unbox(v_____do__lift_1613_);
v_res_1615_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(v_modifyEnv_1604_, v___f_1605_, v_inst_1606_, v_inst_1607_, v_inst_1608_, v_inst_1609_, v_cls_1610_, v_toBind_1611_, v___f_1612_, v_____do__lift_328__boxed_1614_);
return v_res_1615_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___f_1617_; 
v___x_1616_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1617_, 0, v___x_1616_);
return v___f_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v___x_1618_, lean_object* v_toApplicative_1619_, lean_object* v_inst_1620_, lean_object* v_modifyEnv_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_toBind_1625_, lean_object* v_inst_1626_, lean_object* v_____do__lift_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1628_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1629_ = lean_box(1);
v___x_1630_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1618_, v___x_1628_, v_____do__lift_1627_, v___x_1629_);
v___x_1631_ = l_List_isEmpty___redArg(v___x_1630_);
lean_dec(v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v_toPure_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec(v_inst_1626_);
lean_dec(v_toBind_1625_);
lean_dec(v_inst_1624_);
lean_dec_ref(v_inst_1623_);
lean_dec_ref(v_inst_1622_);
lean_dec(v_modifyEnv_1621_);
lean_dec_ref(v_inst_1620_);
v_toPure_1632_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc(v_toPure_1632_);
lean_dec_ref(v_toApplicative_1619_);
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_apply_2(v_toPure_1632_, lean_box(0), v___x_1633_);
return v___x_1634_;
}
else
{
lean_object* v_getInheritedTraceOptions_1635_; lean_object* v_toPure_1636_; lean_object* v___f_1637_; lean_object* v___f_1638_; lean_object* v_cls_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_getInheritedTraceOptions_1635_ = lean_ctor_get(v_inst_1620_, 2);
lean_inc(v_getInheritedTraceOptions_1635_);
v_toPure_1636_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc(v_toPure_1636_);
lean_dec_ref(v_toApplicative_1619_);
v___f_1637_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0);
lean_inc(v_modifyEnv_1621_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1638_, 0, v_modifyEnv_1621_);
lean_closure_set(v___f_1638_, 1, v___f_1637_);
v_cls_1639_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1625_, 3);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1640_, 0, v_modifyEnv_1621_);
lean_closure_set(v___f_1640_, 1, v___f_1637_);
lean_closure_set(v___f_1640_, 2, v_inst_1622_);
lean_closure_set(v___f_1640_, 3, v_inst_1620_);
lean_closure_set(v___f_1640_, 4, v_inst_1623_);
lean_closure_set(v___f_1640_, 5, v_inst_1624_);
lean_closure_set(v___f_1640_, 6, v_cls_1639_);
lean_closure_set(v___f_1640_, 7, v_toBind_1625_);
lean_closure_set(v___f_1640_, 8, v___f_1638_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1641_, 0, v_toPure_1636_);
lean_closure_set(v___f_1641_, 1, v_cls_1639_);
lean_closure_set(v___f_1641_, 2, v_toBind_1625_);
lean_closure_set(v___f_1641_, 3, v_inst_1626_);
v___x_1642_ = lean_apply_4(v_toBind_1625_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1635_, v___f_1641_);
v___x_1643_ = lean_apply_4(v_toBind_1625_, lean_box(0), lean_box(0), v___x_1642_, v___f_1640_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_inst_1649_){
_start:
{
lean_object* v_toApplicative_1650_; lean_object* v_toBind_1651_; lean_object* v_getEnv_1652_; lean_object* v_modifyEnv_1653_; lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___x_1656_; 
v_toApplicative_1650_ = lean_ctor_get(v_inst_1644_, 0);
lean_inc_ref(v_toApplicative_1650_);
v_toBind_1651_ = lean_ctor_get(v_inst_1644_, 1);
lean_inc_n(v_toBind_1651_, 2);
v_getEnv_1652_ = lean_ctor_get(v_inst_1645_, 0);
lean_inc(v_getEnv_1652_);
v_modifyEnv_1653_ = lean_ctor_get(v_inst_1645_, 1);
lean_inc(v_modifyEnv_1653_);
lean_dec_ref(v_inst_1645_);
v___x_1654_ = lean_box(0);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4), 10, 9);
lean_closure_set(v___f_1655_, 0, v___x_1654_);
lean_closure_set(v___f_1655_, 1, v_toApplicative_1650_);
lean_closure_set(v___f_1655_, 2, v_inst_1646_);
lean_closure_set(v___f_1655_, 3, v_modifyEnv_1653_);
lean_closure_set(v___f_1655_, 4, v_inst_1644_);
lean_closure_set(v___f_1655_, 5, v_inst_1648_);
lean_closure_set(v___f_1655_, 6, v_inst_1649_);
lean_closure_set(v___f_1655_, 7, v_toBind_1651_);
lean_closure_set(v___f_1655_, 8, v_inst_1647_);
v___x_1656_ = lean_apply_4(v_toBind_1651_, lean_box(0), lean_box(0), v_getEnv_1652_, v___f_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1658_, v_inst_1659_, v_inst_1660_, v_inst_1661_, v_inst_1662_, v_inst_1663_);
return v___x_1664_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(4259277863u);
v___x_1680_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1681_ = l_Lean_Name_num___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1684_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1685_ = l_Lean_Name_str___override(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1689_ = l_Lean_Name_str___override(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_unsigned_to_nat(2u);
v___x_1691_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
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
v___x_1696_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
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
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_indirectModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_indirectModUseExt);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_extraModUses = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_extraModUses);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
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
