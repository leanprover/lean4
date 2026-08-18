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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_m_22_, lean_object* v_query_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_zero_27_; uint8_t v_isZero_28_; 
v_zero_27_ = lean_unsigned_to_nat(0u);
v_isZero_28_ = lean_nat_dec_eq(v_x_25_, v_zero_27_);
if (v_isZero_28_ == 1)
{
lean_dec(v_x_26_);
lean_dec(v_x_25_);
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(2);
return v___x_29_;
}
else
{
lean_object* v_val_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_val_30_ = lean_ctor_get(v_x_24_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v_x_24_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v_x_24_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_val_30_);
lean_dec(v_x_24_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_val_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v_keyArray_38_; lean_object* v_valueArray_39_; lean_object* v___x_40_; uint8_t v_isSome_41_; 
v_keyArray_38_ = lean_ctor_get(v_m_22_, 1);
v_valueArray_39_ = lean_ctor_get(v_m_22_, 2);
v___x_40_ = lean_array_fget_borrowed(v_keyArray_38_, v_x_26_);
v_isSome_41_ = lean_noption_is_some(v___x_40_);
if (v_isSome_41_ == 0)
{
lean_dec(v_x_25_);
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v_x_26_);
return v___x_42_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
lean_dec(v_x_26_);
v_val_43_ = lean_ctor_get(v_x_24_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_24_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v_x_24_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_val_43_);
lean_dec(v_x_24_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_val_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
else
{
lean_object* v_one_51_; lean_object* v_n_52_; lean_object* v___y_54_; 
v_one_51_ = lean_unsigned_to_nat(1u);
v_n_52_ = lean_nat_sub(v_x_25_, v_one_51_);
lean_dec(v_x_25_);
if (v_isSome_41_ == 0)
{
goto v___jp_60_;
}
else
{
lean_object* v___x_62_; uint8_t v_isSome_63_; 
v___x_62_ = lean_array_fget_borrowed(v_valueArray_39_, v_x_26_);
v_isSome_63_ = lean_noption_is_some(v___x_62_);
if (v_isSome_63_ == 0)
{
goto v___jp_60_;
}
else
{
lean_object* v_val_64_; uint8_t v___x_65_; 
lean_inc(v___x_40_);
v_val_64_ = lean_noption_get(v___x_40_);
v___x_65_ = lean_name_eq(v_val_64_, v_query_23_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
lean_dec(v_val_64_);
v___x_66_ = lean_array_get_size(v_keyArray_38_);
v___x_67_ = lean_nat_add(v_x_26_, v_one_51_);
lean_dec(v_x_26_);
v___x_68_ = lean_nat_dec_lt(v___x_67_, v___x_66_);
if (v___x_68_ == 0)
{
lean_dec(v___x_67_);
v_x_25_ = v_n_52_;
v_x_26_ = v_zero_27_;
goto _start;
}
else
{
v_x_25_ = v_n_52_;
v_x_26_ = v___x_67_;
goto _start;
}
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
lean_dec(v_n_52_);
lean_dec(v_x_24_);
lean_inc(v___x_62_);
v_val_71_ = lean_noption_get(v___x_62_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_x_26_);
lean_ctor_set(v___x_72_, 1, v_val_64_);
lean_ctor_set(v___x_72_, 2, v_val_71_);
return v___x_72_;
}
}
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = lean_array_get_size(v_keyArray_38_);
v___x_56_ = lean_nat_add(v_x_26_, v_one_51_);
lean_dec(v_x_26_);
v___x_57_ = lean_nat_dec_lt(v___x_56_, v___x_55_);
if (v___x_57_ == 0)
{
lean_dec(v___x_56_);
v_x_24_ = v___y_54_;
v_x_25_ = v_n_52_;
v_x_26_ = v_zero_27_;
goto _start;
}
else
{
v_x_24_ = v___y_54_;
v_x_25_ = v_n_52_;
v_x_26_ = v___x_56_;
goto _start;
}
}
v___jp_60_:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_61_; 
lean_inc(v_x_26_);
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v_x_26_);
v___y_54_ = v___x_61_;
goto v___jp_53_;
}
else
{
v___y_54_ = v_x_24_;
goto v___jp_53_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_m_73_, lean_object* v_query_74_, lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_73_, v_query_74_, v_x_75_, v_x_76_, v_x_77_);
lean_dec(v_query_74_);
lean_dec_ref(v_m_73_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_79_, lean_object* v_query_80_){
_start:
{
lean_object* v_keyArray_81_; lean_object* v___x_82_; uint64_t v___y_84_; 
v_keyArray_81_ = lean_ctor_get(v_m_79_, 1);
v___x_82_ = lean_array_get_size(v_keyArray_81_);
if (lean_obj_tag(v_query_80_) == 0)
{
uint64_t v___x_99_; 
v___x_99_ = 1723ULL;
v___y_84_ = v___x_99_;
goto v___jp_83_;
}
else
{
uint64_t v_hash_100_; 
v_hash_100_ = lean_ctor_get_uint64(v_query_80_, sizeof(void*)*2);
v___y_84_ = v_hash_100_;
goto v___jp_83_;
}
v___jp_83_:
{
uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v_fold_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_85_ = 32ULL;
v___x_86_ = lean_uint64_shift_right(v___y_84_, v___x_85_);
v_fold_87_ = lean_uint64_xor(v___y_84_, v___x_86_);
v___x_88_ = 16ULL;
v___x_89_ = lean_uint64_shift_right(v_fold_87_, v___x_88_);
v___x_90_ = lean_uint64_xor(v_fold_87_, v___x_89_);
v___x_91_ = lean_uint64_to_usize(v___x_90_);
v___x_92_ = lean_usize_of_nat(v___x_82_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_sub(v___x_92_, v___x_93_);
v___x_95_ = lean_usize_land(v___x_91_, v___x_94_);
v___x_96_ = lean_usize_to_nat(v___x_95_);
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_79_, v_query_80_, v___x_97_, v___x_82_, v___x_96_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_101_, lean_object* v_query_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(v_m_101_, v_query_102_);
lean_dec(v_query_102_);
lean_dec_ref(v_m_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0(lean_object* v_val_106_, lean_object* v_x_107_){
_start:
{
lean_object* v___y_109_; 
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0___closed__0));
v___y_109_ = v___x_112_;
goto v___jp_108_;
}
else
{
lean_object* v_val_113_; 
v_val_113_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v_x_107_, 1);
v___y_109_ = v_val_113_;
goto v___jp_108_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_array_push(v___y_109_, v_val_106_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_b_114_, lean_object* v_acc_115_, lean_object* v_i_116_){
_start:
{
lean_object* v___y_118_; lean_object* v_keyArray_126_; lean_object* v_valueArray_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_keyArray_126_ = lean_ctor_get(v_b_114_, 1);
v_valueArray_127_ = lean_ctor_get(v_b_114_, 2);
v___x_128_ = lean_array_get_size(v_keyArray_126_);
v___x_129_ = lean_nat_dec_lt(v_i_116_, v___x_128_);
if (v___x_129_ == 0)
{
lean_dec(v_i_116_);
return v_acc_115_;
}
else
{
lean_object* v___x_130_; uint8_t v_isSome_131_; 
v___x_130_ = lean_array_fget_borrowed(v_keyArray_126_, v_i_116_);
v_isSome_131_ = lean_noption_is_some(v___x_130_);
if (v_isSome_131_ == 0)
{
goto v___jp_122_;
}
else
{
lean_object* v___x_132_; uint8_t v_isSome_133_; 
v___x_132_ = lean_array_fget_borrowed(v_valueArray_127_, v_i_116_);
v_isSome_133_ = lean_noption_is_some(v___x_132_);
if (v_isSome_133_ == 0)
{
goto v___jp_122_;
}
else
{
lean_object* v_val_134_; lean_object* v_val_135_; lean_object* v_i_137_; lean_object* v___x_142_; 
lean_inc(v___x_130_);
v_val_134_ = lean_noption_get(v___x_130_);
lean_inc(v___x_132_);
v_val_135_ = lean_noption_get(v___x_132_);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(v_acc_115_, v_val_134_);
switch(lean_obj_tag(v___x_142_))
{
case 0:
{
lean_object* v_index_143_; lean_object* v_size_144_; lean_object* v___x_145_; 
v_index_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_143_);
lean_dec_ref_known(v___x_142_, 3);
v_size_144_ = lean_ctor_get(v_acc_115_, 0);
lean_inc(v_size_144_);
v___x_145_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_115_, v_size_144_, v_index_143_, v_val_134_, v_val_135_);
lean_dec(v_index_143_);
v___y_118_ = v___x_145_;
goto v___jp_117_;
}
case 1:
{
lean_object* v_index_146_; 
v_index_146_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_146_);
lean_dec_ref_known(v___x_142_, 1);
v_i_137_ = v_index_146_;
goto v___jp_136_;
}
default: 
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_115_, v___x_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_index_149_; 
v_index_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_index_149_);
lean_dec_ref_known(v___x_148_, 1);
v_i_137_ = v_index_149_;
goto v___jp_136_;
}
else
{
lean_dec(v_val_135_);
lean_dec(v_val_134_);
v___y_118_ = v_acc_115_;
goto v___jp_117_;
}
}
}
v___jp_136_:
{
lean_object* v_size_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_size_138_ = lean_ctor_get(v_acc_115_, 0);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_add(v_size_138_, v___x_139_);
v___x_141_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_115_, v___x_140_, v_i_137_, v_val_134_, v_val_135_);
lean_dec(v_i_137_);
v___y_118_ = v___x_141_;
goto v___jp_117_;
}
}
}
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_116_, v___x_119_);
lean_dec(v_i_116_);
v_acc_115_ = v___y_118_;
v_i_116_ = v___x_120_;
goto _start;
}
v___jp_122_:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_i_116_, v___x_123_);
lean_dec(v_i_116_);
v_i_116_ = v___x_124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_150_, lean_object* v_acc_151_, lean_object* v_i_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_150_, v_acc_151_, v_i_152_);
lean_dec_ref(v_b_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_init_154_, lean_object* v_b_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_155_, v_init_154_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_init_158_, lean_object* v_b_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg(v_init_158_, v_b_159_);
lean_dec_ref(v_b_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_161_){
_start:
{
lean_object* v_keyArray_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_cellCount_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_target_169_; lean_object* v___x_170_; 
v_keyArray_162_ = lean_ctor_get(v_m_161_, 1);
v___x_163_ = lean_array_get_size(v_keyArray_162_);
v___x_164_ = lean_unsigned_to_nat(2u);
v_cellCount_165_ = lean_nat_mul(v___x_163_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_165_);
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_165_);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_165_);
v_target_169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_169_, 0, v___x_166_);
lean_ctor_set(v_target_169_, 1, v___x_167_);
lean_ctor_set(v_target_169_, 2, v___x_168_);
v___x_170_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg(v_target_169_, v_m_161_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(v_m_171_);
lean_dec_ref(v_m_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_val_173_, lean_object* v_as_174_, size_t v_sz_175_, size_t v_i_176_, lean_object* v_b_177_){
_start:
{
lean_object* v___y_179_; uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_lt(v_i_176_, v_sz_175_);
if (v___x_183_ == 0)
{
lean_dec(v_val_173_);
return v_b_177_;
}
else
{
lean_object* v_a_184_; lean_object* v_declName_185_; lean_object* v___x_186_; 
v_a_184_ = lean_array_uget_borrowed(v_as_174_, v_i_176_);
v_declName_185_ = lean_ctor_get(v_a_184_, 1);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(v_b_177_, v_declName_185_);
switch(lean_obj_tag(v___x_186_))
{
case 0:
{
lean_object* v_index_187_; lean_object* v_value_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_index_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_index_187_);
v_value_188_ = lean_ctor_get(v___x_186_, 2);
lean_inc(v_value_188_);
lean_dec_ref_known(v___x_186_, 3);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_value_188_);
lean_inc(v_val_173_);
v___x_190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0(v_val_173_, v___x_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_size_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_size_191_ = lean_ctor_get(v_b_177_, 0);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_sub(v_size_191_, v___x_192_);
v___x_194_ = l_Std_DHashMap_Raw_clearCell___redArg(v_b_177_, v___x_193_, v_index_187_);
lean_dec(v_index_187_);
v___y_179_ = v___x_194_;
goto v___jp_178_;
}
else
{
lean_object* v_val_195_; lean_object* v_size_196_; lean_object* v___x_197_; 
v_val_195_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v___x_190_, 1);
v_size_196_ = lean_ctor_get(v_b_177_, 0);
lean_inc(v_size_196_);
lean_inc(v_declName_185_);
v___x_197_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_177_, v_size_196_, v_index_187_, v_declName_185_, v_val_195_);
lean_dec(v_index_187_);
v___y_179_ = v___x_197_;
goto v___jp_178_;
}
}
case 1:
{
lean_object* v_index_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_index_198_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_index_198_);
lean_dec_ref_known(v___x_186_, 1);
v___x_199_ = lean_box(0);
lean_inc(v_val_173_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0(v_val_173_, v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_dec(v_index_198_);
v___y_179_ = v_b_177_;
goto v___jp_178_;
}
else
{
lean_object* v_val_201_; lean_object* v___y_203_; lean_object* v_i_204_; lean_object* v_size_219_; lean_object* v_keyArray_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_val_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_200_, 1);
v_size_219_ = lean_ctor_get(v_b_177_, 0);
v_keyArray_220_ = lean_ctor_get(v_b_177_, 1);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_size_219_, v___x_221_);
v___x_223_ = lean_array_get_size(v_keyArray_220_);
v___x_224_ = lean_nat_dec_lt(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v___x_222_);
lean_dec(v_index_198_);
goto v___jp_209_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_225_ = lean_unsigned_to_nat(4u);
v___x_226_ = lean_nat_mul(v___x_222_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(3u);
v___x_228_ = lean_nat_mul(v___x_223_, v___x_227_);
v___x_229_ = lean_nat_dec_le(v___x_226_, v___x_228_);
lean_dec(v___x_228_);
lean_dec(v___x_226_);
if (v___x_229_ == 0)
{
lean_dec(v___x_222_);
lean_dec(v_index_198_);
goto v___jp_209_;
}
else
{
lean_object* v___x_230_; 
lean_inc(v_declName_185_);
v___x_230_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_177_, v___x_222_, v_index_198_, v_declName_185_, v_val_201_);
lean_dec(v_index_198_);
v___y_179_ = v___x_230_;
goto v___jp_178_;
}
}
v___jp_202_:
{
lean_object* v_size_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_size_205_ = lean_ctor_get(v___y_203_, 0);
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_size_205_, v___x_206_);
lean_inc(v_declName_185_);
v___x_208_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_203_, v___x_207_, v_i_204_, v_declName_185_, v_val_201_);
lean_dec(v_i_204_);
v___y_179_ = v___x_208_;
goto v___jp_178_;
}
v___jp_209_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(v_b_177_);
lean_dec_ref(v_b_177_);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(v___x_210_, v_declName_185_);
switch(lean_obj_tag(v___x_211_))
{
case 0:
{
lean_object* v_index_212_; lean_object* v_size_213_; lean_object* v___x_214_; 
v_index_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_index_212_);
lean_dec_ref_known(v___x_211_, 3);
v_size_213_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_size_213_);
lean_inc(v_declName_185_);
v___x_214_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_210_, v_size_213_, v_index_212_, v_declName_185_, v_val_201_);
lean_dec(v_index_212_);
v___y_179_ = v___x_214_;
goto v___jp_178_;
}
case 1:
{
lean_object* v_index_215_; 
v_index_215_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_index_215_);
lean_dec_ref_known(v___x_211_, 1);
v___y_203_ = v___x_210_;
v_i_204_ = v_index_215_;
goto v___jp_202_;
}
default: 
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_210_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_index_218_; 
v_index_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_index_218_);
lean_dec_ref_known(v___x_217_, 1);
v___y_203_ = v___x_210_;
v_i_204_ = v_index_218_;
goto v___jp_202_;
}
else
{
lean_dec(v_val_201_);
v___y_179_ = v___x_210_;
goto v___jp_178_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(0);
lean_inc(v_val_173_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0(v_val_173_, v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
v___y_179_ = v_b_177_;
goto v___jp_178_;
}
else
{
lean_object* v_val_233_; lean_object* v___y_235_; lean_object* v_i_236_; lean_object* v___y_242_; lean_object* v_size_251_; lean_object* v_keyArray_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_val_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_232_, 1);
v_size_251_ = lean_ctor_get(v_b_177_, 0);
v_keyArray_252_ = lean_ctor_get(v_b_177_, 1);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_size_251_, v___x_253_);
v___x_255_ = lean_array_get_size(v_keyArray_252_);
v___x_256_ = lean_nat_dec_lt(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v___x_254_);
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(v_b_177_);
lean_dec_ref(v_b_177_);
v___y_242_ = v___x_257_;
goto v___jp_241_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_258_ = lean_unsigned_to_nat(4u);
v___x_259_ = lean_nat_mul(v___x_254_, v___x_258_);
lean_dec(v___x_254_);
v___x_260_ = lean_unsigned_to_nat(3u);
v___x_261_ = lean_nat_mul(v___x_255_, v___x_260_);
v___x_262_ = lean_nat_dec_le(v___x_259_, v___x_261_);
lean_dec(v___x_261_);
lean_dec(v___x_259_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(v_b_177_);
lean_dec_ref(v_b_177_);
v___y_242_ = v___x_263_;
goto v___jp_241_;
}
else
{
v___y_242_ = v_b_177_;
goto v___jp_241_;
}
}
v___jp_234_:
{
lean_object* v_size_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_size_237_ = lean_ctor_get(v___y_235_, 0);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_size_237_, v___x_238_);
lean_inc(v_declName_185_);
v___x_240_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_235_, v___x_239_, v_i_236_, v_declName_185_, v_val_233_);
lean_dec(v_i_236_);
v___y_179_ = v___x_240_;
goto v___jp_178_;
}
v___jp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(v___y_242_, v_declName_185_);
switch(lean_obj_tag(v___x_243_))
{
case 0:
{
lean_object* v_index_244_; lean_object* v_size_245_; lean_object* v___x_246_; 
v_index_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_index_244_);
lean_dec_ref_known(v___x_243_, 3);
v_size_245_ = lean_ctor_get(v___y_242_, 0);
lean_inc(v_size_245_);
lean_inc(v_declName_185_);
v___x_246_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_242_, v_size_245_, v_index_244_, v_declName_185_, v_val_233_);
lean_dec(v_index_244_);
v___y_179_ = v___x_246_;
goto v___jp_178_;
}
case 1:
{
lean_object* v_index_247_; 
v_index_247_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_index_247_);
lean_dec_ref_known(v___x_243_, 1);
v___y_235_ = v___y_242_;
v_i_236_ = v_index_247_;
goto v___jp_234_;
}
default: 
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_242_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_index_250_; 
v_index_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_index_250_);
lean_dec_ref_known(v___x_249_, 1);
v___y_235_ = v___y_242_;
v_i_236_ = v_index_250_;
goto v___jp_234_;
}
else
{
lean_dec(v_val_233_);
v___y_179_ = v___y_242_;
goto v___jp_178_;
}
}
}
}
}
}
}
}
v___jp_178_:
{
size_t v___x_180_; size_t v___x_181_; 
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_add(v_i_176_, v___x_180_);
v_i_176_ = v___x_181_;
v_b_177_ = v___y_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_val_264_, lean_object* v_as_265_, lean_object* v_sz_266_, lean_object* v_i_267_, lean_object* v_b_268_){
_start:
{
size_t v_sz_boxed_269_; size_t v_i_boxed_270_; lean_object* v_res_271_; 
v_sz_boxed_269_ = lean_unbox_usize(v_sz_266_);
lean_dec(v_sz_266_);
v_i_boxed_270_ = lean_unbox_usize(v_i_267_);
lean_dec(v_i_267_);
v_res_271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_val_264_, v_as_265_, v_sz_boxed_269_, v_i_boxed_270_, v_b_268_);
lean_dec_ref(v_as_265_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__3(lean_object* v_as_272_, size_t v_sz_273_, size_t v_i_274_, lean_object* v_b_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_lt(v_i_274_, v_sz_273_);
if (v___x_276_ == 0)
{
return v_b_275_;
}
else
{
lean_object* v_snd_277_; 
v_snd_277_ = lean_ctor_get(v_b_275_, 1);
lean_inc(v_snd_277_);
if (lean_obj_tag(v_snd_277_) == 0)
{
lean_object* v_fst_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_fst_278_ = lean_ctor_get(v_b_275_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_b_275_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_b_275_, 1);
lean_dec(v_unused_286_);
v___x_280_ = v_b_275_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_fst_278_);
lean_dec(v_b_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_fst_278_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_snd_277_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_fst_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_311_; 
v_fst_287_ = lean_ctor_get(v_b_275_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_b_275_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_b_275_, 1);
lean_dec(v_unused_312_);
v___x_289_ = v_b_275_;
v_isShared_290_ = v_isSharedCheck_311_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_fst_287_);
lean_dec(v_b_275_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_311_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_val_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_310_; 
v_val_291_ = lean_ctor_get(v_snd_277_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_snd_277_);
if (v_isSharedCheck_310_ == 0)
{
v___x_293_ = v_snd_277_;
v_isShared_294_ = v_isSharedCheck_310_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_val_291_);
lean_dec(v_snd_277_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_310_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v_a_295_ = lean_array_uget_borrowed(v_as_272_, v_i_274_);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_val_291_, v___x_296_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_299_ = v___x_293_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_309_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
size_t v_sz_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v_sz_300_ = lean_array_size(v_a_295_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_val_291_, v_a_295_, v_sz_300_, v___x_301_, v_fst_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_299_);
lean_ctor_set(v___x_289_, 0, v___x_302_);
v___x_304_ = v___x_289_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_299_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
size_t v___x_305_; size_t v___x_306_; 
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_274_, v___x_305_);
v_i_274_ = v___x_306_;
v_b_275_ = v___x_304_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__3___boxed(lean_object* v_as_313_, lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_b_316_){
_start:
{
size_t v_sz_boxed_317_; size_t v_i_boxed_318_; lean_object* v_res_319_; 
v_sz_boxed_317_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_318_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__3(v_as_313_, v_sz_boxed_317_, v_i_boxed_318_, v_b_316_);
lean_dec_ref(v_as_313_);
return v_res_319_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_320_; lean_object* v___x_321_; 
v_cellCount_320_ = lean_unsigned_to_nat(16u);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_320_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_322_; lean_object* v___x_323_; 
v_cellCount_322_ = lean_unsigned_to_nat(16u);
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_322_);
return v___x_323_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_s_327_; 
v___x_324_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_325_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_326_ = lean_unsigned_to_nat(0u);
v_s_327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_s_327_, 0, v___x_326_);
lean_ctor_set(v_s_327_, 1, v___x_325_);
lean_ctor_set(v_s_327_, 2, v___x_324_);
return v_s_327_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_330_; lean_object* v_s_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_331_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_s_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_333_){
_start:
{
lean_object* v___x_334_; size_t v_sz_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v_fst_338_; 
v___x_334_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_335_ = lean_array_size(v_es_333_);
v___x_336_ = ((size_t)0ULL);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__3(v_es_333_, v_sz_335_, v___x_336_, v___x_334_);
v_fst_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_fst_338_);
lean_dec_ref(v___x_337_);
return v_fst_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_339_);
lean_dec_ref(v_es_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_358_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_361_, lean_object* v_m_362_, lean_object* v_query_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___redArg(v_m_362_, v_query_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_365_, lean_object* v_m_366_, lean_object* v_query_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_00_u03b2_365_, v_m_366_, v_query_367_);
lean_dec(v_query_367_);
lean_dec_ref(v_m_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_369_, lean_object* v_m_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___redArg(v_m_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_372_, lean_object* v_m_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_00_u03b2_372_, v_m_373_);
lean_dec_ref(v_m_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_375_, lean_object* v_m_376_, lean_object* v_query_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_376_, v_query_377_, v_x_378_, v_x_379_, v_x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_383_, lean_object* v_m_384_, lean_object* v_query_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_383_, v_m_384_, v_query_385_, v_x_386_, v_x_387_, v_x_388_, v_x_389_);
lean_dec(v_query_385_);
lean_dec_ref(v_m_384_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_391_, lean_object* v_init_392_, lean_object* v_b_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___redArg(v_init_392_, v_b_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_395_, lean_object* v_init_396_, lean_object* v_b_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_395_, v_init_396_, v_b_397_);
lean_dec_ref(v_b_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03b2_399_, lean_object* v_b_400_, lean_object* v_acc_401_, lean_object* v_i_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_400_, v_acc_401_, v_i_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_404_, lean_object* v_b_405_, lean_object* v_acc_406_, lean_object* v_i_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_404_, v_b_405_, v_acc_406_, v_i_407_);
lean_dec_ref(v_b_405_);
return v_res_408_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__2(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_412_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_413_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__3(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object* v_env_417_, lean_object* v_modIdx_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__3, &l_Lean_getIndirectModUses___closed__3_once, _init_l_Lean_getIndirectModUses___closed__3);
v___x_420_ = l_Lean_indirectModUseExt;
v___x_421_ = 0;
v___x_422_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_419_, v___x_420_, v_env_417_, v_modIdx_418_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object* v_env_423_, lean_object* v_modIdx_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_getIndirectModUses(v_env_423_, v_modIdx_424_);
lean_dec(v_modIdx_424_);
lean_dec_ref(v_env_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object* v___x_426_, lean_object* v___x_427_, lean_object* v_x_428_){
_start:
{
lean_object* v_toEnvExtension_429_; lean_object* v_asyncMode_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_toEnvExtension_429_ = lean_ctor_get(v___x_426_, 0);
v_asyncMode_430_ = lean_ctor_get(v_toEnvExtension_429_, 2);
lean_inc(v_asyncMode_430_);
v___x_431_ = lean_box(0);
v___x_432_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_426_, v_x_428_, v___x_427_, v_asyncMode_430_, v___x_431_);
lean_dec(v_asyncMode_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object* v_modifyEnv_433_, lean_object* v___f_434_, lean_object* v_____r_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_apply_1(v_modifyEnv_433_, v___f_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__0));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__2));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__4));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object* v_modifyEnv_446_, lean_object* v___f_447_, lean_object* v_declName_448_, lean_object* v_kind_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_cls_454_, lean_object* v_toBind_455_, lean_object* v___f_456_, uint8_t v_____do__lift_457_){
_start:
{
if (v_____do__lift_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v___f_456_);
lean_dec(v_toBind_455_);
lean_dec(v_cls_454_);
lean_dec(v_inst_453_);
lean_dec_ref(v_inst_452_);
lean_dec_ref(v_inst_451_);
lean_dec_ref(v_inst_450_);
lean_dec_ref(v_kind_449_);
lean_dec(v_declName_448_);
v___x_458_ = lean_apply_1(v_modifyEnv_446_, v___f_447_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v___f_447_);
lean_dec(v_modifyEnv_446_);
v___x_459_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__1, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1);
v___x_460_ = l_Lean_MessageData_ofName(v_declName_448_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__3, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__3_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_stringToMessageData(v_kind_449_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__5, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__5_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_addTrace___redArg(v_inst_450_, v_inst_451_, v_inst_452_, v_inst_453_, v_cls_454_, v___x_467_);
v___x_469_ = lean_apply_4(v_toBind_455_, lean_box(0), lean_box(0), v___x_468_, v___f_456_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object* v_modifyEnv_470_, lean_object* v___f_471_, lean_object* v_declName_472_, lean_object* v_kind_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_cls_478_, lean_object* v_toBind_479_, lean_object* v___f_480_, lean_object* v_____do__lift_481_){
_start:
{
uint8_t v_____do__lift_579__boxed_482_; lean_object* v_res_483_; 
v_____do__lift_579__boxed_482_ = lean_unbox(v_____do__lift_481_);
v_res_483_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_modifyEnv_470_, v___f_471_, v_declName_472_, v_kind_473_, v_inst_474_, v_inst_475_, v_inst_476_, v_inst_477_, v_cls_478_, v_toBind_479_, v___f_480_, v_____do__lift_579__boxed_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v_toPure_487_, lean_object* v_cls_488_, lean_object* v_____do__lift_489_, lean_object* v_____do__lift_490_){
_start:
{
uint8_t v_hasTrace_491_; 
v_hasTrace_491_ = lean_ctor_get_uint8(v_____do__lift_490_, sizeof(void*)*1);
if (v_hasTrace_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v_cls_488_);
v___x_492_ = lean_box(v_hasTrace_491_);
v___x_493_ = lean_apply_2(v_toPure_487_, lean_box(0), v___x_492_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
v___x_495_ = l_Lean_Name_append(v___x_494_, v_cls_488_);
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_489_, v_____do__lift_490_, v___x_495_);
lean_dec(v___x_495_);
v___x_497_ = lean_box(v___x_496_);
v___x_498_ = lean_apply_2(v_toPure_487_, lean_box(0), v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___boxed(lean_object* v_toPure_499_, lean_object* v_cls_500_, lean_object* v_____do__lift_501_, lean_object* v_____do__lift_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_recordIndirectModUse___redArg___lam__3(v_toPure_499_, v_cls_500_, v_____do__lift_501_, v_____do__lift_502_);
lean_dec_ref(v_____do__lift_502_);
lean_dec_ref(v_____do__lift_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object* v_toPure_504_, lean_object* v_cls_505_, lean_object* v_toBind_506_, lean_object* v_inst_507_, lean_object* v_____do__lift_508_){
_start:
{
lean_object* v___f_509_; lean_object* v___x_510_; 
v___f_509_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_509_, 0, v_toPure_504_);
lean_closure_set(v___f_509_, 1, v_cls_505_);
lean_closure_set(v___f_509_, 2, v_____do__lift_508_);
v___x_510_ = lean_apply_4(v_toBind_506_, lean_box(0), lean_box(0), v_inst_507_, v___f_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v___x_514_, lean_object* v_kind_515_, lean_object* v_declName_516_, lean_object* v___x_517_, lean_object* v_inst_518_, lean_object* v_toApplicative_519_, lean_object* v_modifyEnv_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_toBind_524_, lean_object* v_inst_525_, lean_object* v_____do__lift_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_527_ = l_Lean_indirectModUseExt;
v___x_528_ = lean_box(2);
v___x_529_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_514_, v___x_527_, v_____do__lift_526_, v___x_528_);
lean_inc(v_declName_516_);
lean_inc_ref(v_kind_515_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_kind_515_);
lean_ctor_set(v___x_530_, 1, v_declName_516_);
lean_inc_ref(v___x_530_);
v___x_531_ = l_List_elem___redArg(v___x_517_, v___x_530_, v___x_529_);
if (v___x_531_ == 0)
{
lean_object* v_getInheritedTraceOptions_532_; lean_object* v_toPure_533_; lean_object* v___f_534_; lean_object* v___f_535_; lean_object* v_cls_536_; lean_object* v___f_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_getInheritedTraceOptions_532_ = lean_ctor_get(v_inst_518_, 2);
lean_inc(v_getInheritedTraceOptions_532_);
v_toPure_533_ = lean_ctor_get(v_toApplicative_519_, 1);
lean_inc(v_toPure_533_);
lean_dec_ref(v_toApplicative_519_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_534_, 0, v___x_527_);
lean_closure_set(v___f_534_, 1, v___x_530_);
lean_inc_ref(v___f_534_);
lean_inc(v_modifyEnv_520_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_535_, 0, v_modifyEnv_520_);
lean_closure_set(v___f_535_, 1, v___f_534_);
v_cls_536_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_524_, 3);
v___f_537_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_537_, 0, v_modifyEnv_520_);
lean_closure_set(v___f_537_, 1, v___f_534_);
lean_closure_set(v___f_537_, 2, v_declName_516_);
lean_closure_set(v___f_537_, 3, v_kind_515_);
lean_closure_set(v___f_537_, 4, v_inst_521_);
lean_closure_set(v___f_537_, 5, v_inst_518_);
lean_closure_set(v___f_537_, 6, v_inst_522_);
lean_closure_set(v___f_537_, 7, v_inst_523_);
lean_closure_set(v___f_537_, 8, v_cls_536_);
lean_closure_set(v___f_537_, 9, v_toBind_524_);
lean_closure_set(v___f_537_, 10, v___f_535_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_538_, 0, v_toPure_533_);
lean_closure_set(v___f_538_, 1, v_cls_536_);
lean_closure_set(v___f_538_, 2, v_toBind_524_);
lean_closure_set(v___f_538_, 3, v_inst_525_);
v___x_539_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_532_, v___f_538_);
v___x_540_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v___x_539_, v___f_537_);
return v___x_540_;
}
else
{
lean_object* v_toPure_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec_ref_known(v___x_530_, 2);
lean_dec(v_inst_525_);
lean_dec(v_toBind_524_);
lean_dec(v_inst_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_inst_521_);
lean_dec(v_modifyEnv_520_);
lean_dec_ref(v_inst_518_);
lean_dec(v_declName_516_);
lean_dec_ref(v_kind_515_);
v_toPure_541_ = lean_ctor_get(v_toApplicative_519_, 1);
lean_inc(v_toPure_541_);
lean_dec_ref(v_toApplicative_519_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_apply_2(v_toPure_541_, lean_box(0), v___x_542_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_kind_550_, lean_object* v_declName_551_){
_start:
{
lean_object* v_toApplicative_552_; lean_object* v_toBind_553_; lean_object* v_getEnv_554_; lean_object* v_modifyEnv_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v_toApplicative_552_ = lean_ctor_get(v_inst_544_, 0);
lean_inc_ref(v_toApplicative_552_);
v_toBind_553_ = lean_ctor_get(v_inst_544_, 1);
lean_inc_n(v_toBind_553_, 2);
v_getEnv_554_ = lean_ctor_get(v_inst_545_, 0);
lean_inc(v_getEnv_554_);
v_modifyEnv_555_ = lean_ctor_get(v_inst_545_, 1);
lean_inc(v_modifyEnv_555_);
lean_dec_ref(v_inst_545_);
v___x_556_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_557_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5), 13, 12);
lean_closure_set(v___f_558_, 0, v___x_557_);
lean_closure_set(v___f_558_, 1, v_kind_550_);
lean_closure_set(v___f_558_, 2, v_declName_551_);
lean_closure_set(v___f_558_, 3, v___x_556_);
lean_closure_set(v___f_558_, 4, v_inst_546_);
lean_closure_set(v___f_558_, 5, v_toApplicative_552_);
lean_closure_set(v___f_558_, 6, v_modifyEnv_555_);
lean_closure_set(v___f_558_, 7, v_inst_544_);
lean_closure_set(v___f_558_, 8, v_inst_548_);
lean_closure_set(v___f_558_, 9, v_inst_549_);
lean_closure_set(v___f_558_, 10, v_toBind_553_);
lean_closure_set(v___f_558_, 11, v_inst_547_);
v___x_559_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v_getEnv_554_, v___f_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_kind_567_, lean_object* v_declName_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_recordIndirectModUse___redArg(v_inst_561_, v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_, v_inst_566_, v_kind_567_, v_declName_568_);
return v___x_569_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v_module_572_; uint8_t v_isExported_573_; uint8_t v_isMeta_574_; lean_object* v_module_575_; uint8_t v_isExported_576_; uint8_t v_isMeta_577_; uint8_t v___y_579_; uint8_t v___x_580_; 
v_module_572_ = lean_ctor_get(v_x_570_, 0);
v_isExported_573_ = lean_ctor_get_uint8(v_x_570_, sizeof(void*)*1);
v_isMeta_574_ = lean_ctor_get_uint8(v_x_570_, sizeof(void*)*1 + 1);
v_module_575_ = lean_ctor_get(v_x_571_, 0);
v_isExported_576_ = lean_ctor_get_uint8(v_x_571_, sizeof(void*)*1);
v_isMeta_577_ = lean_ctor_get_uint8(v_x_571_, sizeof(void*)*1 + 1);
v___x_580_ = lean_name_eq(v_module_572_, v_module_575_);
if (v___x_580_ == 0)
{
return v___x_580_;
}
else
{
if (v_isExported_573_ == 0)
{
if (v_isExported_576_ == 0)
{
v___y_579_ = v___x_580_;
goto v___jp_578_;
}
else
{
return v_isExported_573_;
}
}
else
{
v___y_579_ = v_isExported_576_;
goto v___jp_578_;
}
}
v___jp_578_:
{
if (v___y_579_ == 0)
{
return v___y_579_;
}
else
{
if (v_isMeta_574_ == 0)
{
if (v_isMeta_577_ == 0)
{
return v___y_579_;
}
else
{
return v_isMeta_574_;
}
}
else
{
return v_isMeta_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Lean_instBEqExtraModUse_beq(v_x_581_, v_x_582_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_x_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_587_){
_start:
{
lean_object* v_module_588_; uint8_t v_isExported_589_; uint8_t v_isMeta_590_; uint64_t v___y_592_; uint64_t v___y_593_; uint64_t v___x_599_; uint64_t v___y_601_; 
v_module_588_ = lean_ctor_get(v_x_587_, 0);
v_isExported_589_ = lean_ctor_get_uint8(v_x_587_, sizeof(void*)*1);
v_isMeta_590_ = lean_ctor_get_uint8(v_x_587_, sizeof(void*)*1 + 1);
v___x_599_ = 0ULL;
if (lean_obj_tag(v_module_588_) == 0)
{
uint64_t v___x_605_; 
v___x_605_ = 1723ULL;
v___y_601_ = v___x_605_;
goto v___jp_600_;
}
else
{
uint64_t v_hash_606_; 
v_hash_606_ = lean_ctor_get_uint64(v_module_588_, sizeof(void*)*2);
v___y_601_ = v_hash_606_;
goto v___jp_600_;
}
v___jp_591_:
{
uint64_t v___x_594_; 
v___x_594_ = lean_uint64_mix_hash(v___y_592_, v___y_593_);
if (v_isMeta_590_ == 0)
{
uint64_t v___x_595_; uint64_t v___x_596_; 
v___x_595_ = 13ULL;
v___x_596_ = lean_uint64_mix_hash(v___x_594_, v___x_595_);
return v___x_596_;
}
else
{
uint64_t v___x_597_; uint64_t v___x_598_; 
v___x_597_ = 11ULL;
v___x_598_ = lean_uint64_mix_hash(v___x_594_, v___x_597_);
return v___x_598_;
}
}
v___jp_600_:
{
uint64_t v___x_602_; 
v___x_602_ = lean_uint64_mix_hash(v___x_599_, v___y_601_);
if (v_isExported_589_ == 0)
{
uint64_t v___x_603_; 
v___x_603_ = 13ULL;
v___y_592_ = v___x_602_;
v___y_593_ = v___x_603_;
goto v___jp_591_;
}
else
{
uint64_t v___x_604_; 
v___x_604_ = 11ULL;
v___y_592_ = v___x_602_;
v___y_593_ = v___x_604_;
goto v___jp_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_607_){
_start:
{
uint64_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Lean_instHashableExtraModUse_hash(v_x_607_);
lean_dec_ref(v_x_607_);
v_r_609_ = lean_box_uint64(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_nat_to_int(v_a_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(10u);
v___x_628_ = lean_nat_to_int(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(14u);
v___x_636_ = lean_nat_to_int(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_642_ = lean_string_length(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_644_ = lean_nat_to_int(v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_649_){
_start:
{
lean_object* v_module_650_; uint8_t v_isExported_651_; uint8_t v_isMeta_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_module_650_ = lean_ctor_get(v_x_649_, 0);
lean_inc(v_module_650_);
v_isExported_651_ = lean_ctor_get_uint8(v_x_649_, sizeof(void*)*1);
v_isMeta_652_ = lean_ctor_get_uint8(v_x_649_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_649_);
v___x_653_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_654_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_655_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_Name_reprPrec(v_module_650_, v___x_656_);
v___x_658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_655_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = 0;
v___x_660_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*1, v___x_659_);
v___x_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_654_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_box(1);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_653_);
v___x_669_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_670_ = l_Bool_repr___redArg(v_isExported_651_);
v___x_671_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*1, v___x_659_);
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_668_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_662_);
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_664_);
v___x_676_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_653_);
v___x_679_ = l_Bool_repr___redArg(v_isMeta_652_);
v___x_680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_655_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v___x_659_);
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_678_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_684_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_682_);
v___x_686_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_683_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*1, v___x_659_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_690_, lean_object* v_prec_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_693_, lean_object* v_prec_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_instReprExtraModUse_repr(v_x_693_, v_prec_694_);
lean_dec(v_prec_694_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_698_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_entries_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_709_ = lean_array_mk(v_entries_707_);
v___x_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_entries_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_711_, v_x_712_, v_entries_713_);
lean_dec_ref(v_x_712_);
lean_dec_ref(v_x_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_array_mk(v_es_715_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_box(0));
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_720_);
lean_dec_ref(v_x_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
lean_object* v_ks_726_; lean_object* v_vs_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_751_; 
v_ks_726_ = lean_ctor_get(v_x_722_, 0);
v_vs_727_ = lean_ctor_get(v_x_722_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_722_);
if (v_isSharedCheck_751_ == 0)
{
v___x_729_ = v_x_722_;
v_isShared_730_ = v_isSharedCheck_751_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_vs_727_);
lean_inc(v_ks_726_);
lean_dec(v_x_722_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_751_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_ks_726_);
v___x_732_ = lean_nat_dec_lt(v_x_723_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec(v_x_723_);
v___x_733_ = lean_array_push(v_ks_726_, v_x_724_);
v___x_734_ = lean_array_push(v_vs_727_, v_x_725_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_734_);
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_736_ = v___x_729_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_object* v_k_x27_738_; uint8_t v___x_739_; 
v_k_x27_738_ = lean_array_fget_borrowed(v_ks_726_, v_x_723_);
v___x_739_ = l_Lean_instBEqExtraModUse_beq(v_x_724_, v_k_x27_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_741_; 
if (v_isShared_730_ == 0)
{
v___x_741_ = v___x_729_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_ks_726_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_vs_727_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_add(v_x_723_, v___x_742_);
lean_dec(v_x_723_);
v_x_722_ = v___x_741_;
v_x_723_ = v___x_743_;
goto _start;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_array_fset(v_ks_726_, v_x_723_, v_x_724_);
v___x_747_ = lean_array_fset(v_vs_727_, v_x_723_, v_x_725_);
lean_dec(v_x_723_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_747_);
lean_ctor_set(v___x_729_, 0, v___x_746_);
v___x_749_ = v___x_729_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_752_, lean_object* v_k_753_, lean_object* v_v_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_752_, v___x_755_, v_k_753_, v_v_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_758_, size_t v_x_759_, size_t v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v_es_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v_j_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_es_763_ = lean_ctor_get(v_x_758_, 0);
v___x_764_ = ((size_t)31ULL);
v___x_765_ = lean_usize_land(v_x_759_, v___x_764_);
v_j_766_ = lean_usize_to_nat(v___x_765_);
v___x_767_ = lean_array_get_size(v_es_763_);
v___x_768_ = lean_nat_dec_lt(v_j_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec(v_j_766_);
lean_dec(v_x_762_);
lean_dec_ref(v_x_761_);
return v_x_758_;
}
else
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_807_; 
lean_inc_ref(v_es_763_);
v_isSharedCheck_807_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_x_758_, 0);
lean_dec(v_unused_808_);
v___x_770_ = v_x_758_;
v_isShared_771_ = v_isSharedCheck_807_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_x_758_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_807_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_v_772_; lean_object* v___x_773_; lean_object* v_xs_x27_774_; lean_object* v___y_776_; 
v_v_772_ = lean_array_fget(v_es_763_, v_j_766_);
v___x_773_ = lean_box(0);
v_xs_x27_774_ = lean_array_fset(v_es_763_, v_j_766_, v___x_773_);
switch(lean_obj_tag(v_v_772_))
{
case 0:
{
lean_object* v_key_781_; lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_792_; 
v_key_781_ = lean_ctor_get(v_v_772_, 0);
v_val_782_ = lean_ctor_get(v_v_772_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_v_772_);
if (v_isSharedCheck_792_ == 0)
{
v___x_784_ = v_v_772_;
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_inc(v_key_781_);
lean_dec(v_v_772_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
uint8_t v___x_786_; 
v___x_786_ = l_Lean_instBEqExtraModUse_beq(v_x_761_, v_key_781_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_del_object(v___x_784_);
v___x_787_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_781_, v_val_782_, v_x_761_, v_x_762_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
v___y_776_ = v___x_788_;
goto v___jp_775_;
}
else
{
lean_object* v___x_790_; 
lean_dec(v_val_782_);
lean_dec(v_key_781_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_x_762_);
lean_ctor_set(v___x_784_, 0, v_x_761_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_x_761_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_x_762_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_776_ = v___x_790_;
goto v___jp_775_;
}
}
}
}
case 1:
{
lean_object* v_node_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_805_; 
v_node_793_ = lean_ctor_get(v_v_772_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_v_772_);
if (v_isSharedCheck_805_ == 0)
{
v___x_795_ = v_v_772_;
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_node_793_);
lean_dec(v_v_772_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_797_ = ((size_t)5ULL);
v___x_798_ = lean_usize_shift_right(v_x_759_, v___x_797_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_x_760_, v___x_799_);
v___x_801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_793_, v___x_798_, v___x_800_, v_x_761_, v_x_762_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_801_);
v___x_803_ = v___x_795_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v___y_776_ = v___x_803_;
goto v___jp_775_;
}
}
}
default: 
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_x_761_);
lean_ctor_set(v___x_806_, 1, v_x_762_);
v___y_776_ = v___x_806_;
goto v___jp_775_;
}
}
v___jp_775_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_array_fset(v_xs_x27_774_, v_j_766_, v___y_776_);
lean_dec(v_j_766_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_777_);
v___x_779_ = v___x_770_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
else
{
lean_object* v_ks_809_; lean_object* v_vs_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_830_; 
v_ks_809_ = lean_ctor_get(v_x_758_, 0);
v_vs_810_ = lean_ctor_get(v_x_758_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_830_ == 0)
{
v___x_812_ = v_x_758_;
v_isShared_813_ = v_isSharedCheck_830_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_vs_810_);
lean_inc(v_ks_809_);
lean_dec(v_x_758_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_830_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_ks_809_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_vs_810_);
v___x_815_ = v_reuseFailAlloc_829_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v_newNode_816_; uint8_t v___y_818_; size_t v___x_824_; uint8_t v___x_825_; 
v_newNode_816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_815_, v_x_761_, v_x_762_);
v___x_824_ = ((size_t)7ULL);
v___x_825_ = lean_usize_dec_le(v___x_824_, v_x_760_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_816_);
v___x_827_ = lean_unsigned_to_nat(4u);
v___x_828_ = lean_nat_dec_lt(v___x_826_, v___x_827_);
lean_dec(v___x_826_);
v___y_818_ = v___x_828_;
goto v___jp_817_;
}
else
{
v___y_818_ = v___x_825_;
goto v___jp_817_;
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
lean_object* v_ks_819_; lean_object* v_vs_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_ks_819_ = lean_ctor_get(v_newNode_816_, 0);
lean_inc_ref(v_ks_819_);
v_vs_820_ = lean_ctor_get(v_newNode_816_, 1);
lean_inc_ref(v_vs_820_);
lean_dec_ref(v_newNode_816_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_760_, v_ks_819_, v_vs_820_, v___x_821_, v___x_822_);
lean_dec_ref(v_vs_820_);
lean_dec_ref(v_ks_819_);
return v___x_823_;
}
else
{
return v_newNode_816_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_array_get_size(v_keys_832_);
v___x_837_ = lean_nat_dec_lt(v_i_834_, v___x_836_);
if (v___x_837_ == 0)
{
lean_dec(v_i_834_);
return v_entries_835_;
}
else
{
lean_object* v_k_838_; lean_object* v_v_839_; uint64_t v___x_840_; size_t v_h_841_; size_t v___x_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v_h_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_k_838_ = lean_array_fget_borrowed(v_keys_832_, v_i_834_);
v_v_839_ = lean_array_fget_borrowed(v_vals_833_, v_i_834_);
v___x_840_ = l_Lean_instHashableExtraModUse_hash(v_k_838_);
v_h_841_ = lean_uint64_to_usize(v___x_840_);
v___x_842_ = ((size_t)5ULL);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_sub(v_depth_831_, v___x_844_);
v___x_846_ = lean_usize_mul(v___x_842_, v___x_845_);
v_h_847_ = lean_usize_shift_right(v_h_841_, v___x_846_);
v___x_848_ = lean_nat_add(v_i_834_, v___x_843_);
lean_dec(v_i_834_);
lean_inc(v_v_839_);
lean_inc(v_k_838_);
v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_835_, v_h_847_, v_depth_831_, v_k_838_, v_v_839_);
v_i_834_ = v___x_848_;
v_entries_835_ = v___x_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_851_, lean_object* v_keys_852_, lean_object* v_vals_853_, lean_object* v_i_854_, lean_object* v_entries_855_){
_start:
{
size_t v_depth_boxed_856_; lean_object* v_res_857_; 
v_depth_boxed_856_ = lean_unbox_usize(v_depth_851_);
lean_dec(v_depth_851_);
v_res_857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_856_, v_keys_852_, v_vals_853_, v_i_854_, v_entries_855_);
lean_dec_ref(v_vals_853_);
lean_dec_ref(v_keys_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_567__boxed_863_; size_t v_x_568__boxed_864_; lean_object* v_res_865_; 
v_x_567__boxed_863_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_x_568__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_858_, v_x_567__boxed_863_, v_x_568__boxed_864_, v_x_861_, v_x_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
uint64_t v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; 
v___x_869_ = l_Lean_instHashableExtraModUse_hash(v_x_867_);
v___x_870_ = lean_uint64_to_usize(v___x_869_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_866_, v___x_870_, v___x_871_, v_x_867_, v_x_868_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_873_, lean_object* v_k_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_box(0);
v___x_876_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_873_, v_k_874_, v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_877_, lean_object* v_i_878_, lean_object* v_k_879_){
_start:
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_array_get_size(v_keys_877_);
v___x_881_ = lean_nat_dec_lt(v_i_878_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v_i_878_);
return v___x_881_;
}
else
{
lean_object* v_k_x27_882_; uint8_t v___x_883_; 
v_k_x27_882_ = lean_array_fget_borrowed(v_keys_877_, v_i_878_);
v___x_883_ = l_Lean_instBEqExtraModUse_beq(v_k_879_, v_k_x27_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_i_878_, v___x_884_);
lean_dec(v_i_878_);
v_i_878_ = v___x_885_;
goto _start;
}
else
{
lean_dec(v_i_878_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_887_, lean_object* v_i_888_, lean_object* v_k_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_887_, v_i_888_, v_k_889_);
lean_dec_ref(v_k_889_);
lean_dec_ref(v_keys_887_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_892_, size_t v_x_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_object* v_es_895_; lean_object* v___x_896_; size_t v___x_897_; size_t v___x_898_; lean_object* v_j_899_; lean_object* v___x_900_; 
v_es_895_ = lean_ctor_get(v_x_892_, 0);
v___x_896_ = lean_box(2);
v___x_897_ = ((size_t)31ULL);
v___x_898_ = lean_usize_land(v_x_893_, v___x_897_);
v_j_899_ = lean_usize_to_nat(v___x_898_);
v___x_900_ = lean_array_get_borrowed(v___x_896_, v_es_895_, v_j_899_);
lean_dec(v_j_899_);
switch(lean_obj_tag(v___x_900_))
{
case 0:
{
lean_object* v_key_901_; uint8_t v___x_902_; 
v_key_901_ = lean_ctor_get(v___x_900_, 0);
v___x_902_ = l_Lean_instBEqExtraModUse_beq(v_x_894_, v_key_901_);
return v___x_902_;
}
case 1:
{
lean_object* v_node_903_; size_t v___x_904_; size_t v___x_905_; 
v_node_903_ = lean_ctor_get(v___x_900_, 0);
v___x_904_ = ((size_t)5ULL);
v___x_905_ = lean_usize_shift_right(v_x_893_, v___x_904_);
v_x_892_ = v_node_903_;
v_x_893_ = v___x_905_;
goto _start;
}
default: 
{
uint8_t v___x_907_; 
v___x_907_ = 0;
return v___x_907_;
}
}
}
else
{
lean_object* v_ks_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_ks_908_ = lean_ctor_get(v_x_892_, 0);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_908_, v___x_909_, v_x_894_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
size_t v_x_753__boxed_914_; uint8_t v_res_915_; lean_object* v_r_916_; 
v_x_753__boxed_914_ = lean_unbox_usize(v_x_912_);
lean_dec(v_x_912_);
v_res_915_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_911_, v_x_753__boxed_914_, v_x_913_);
lean_dec_ref(v_x_913_);
lean_dec_ref(v_x_911_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
uint64_t v___x_919_; size_t v___x_920_; uint8_t v___x_921_; 
v___x_919_ = l_Lean_instHashableExtraModUse_hash(v_x_918_);
v___x_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_917_, v___x_920_, v_x_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
uint8_t v_res_924_; lean_object* v_r_925_; 
v_res_924_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_922_, v_x_923_);
lean_dec_ref(v_x_923_);
lean_dec_ref(v_x_922_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_968_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_970_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
uint8_t v_res_978_; lean_object* v_r_979_; 
v_res_978_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_975_, v_x_976_, v_x_977_);
lean_dec_ref(v_x_977_);
lean_dec_ref(v_x_976_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_981_, v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, size_t v_x_987_, lean_object* v_x_988_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_986_, v_x_987_, v_x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
size_t v_x_951__boxed_994_; uint8_t v_res_995_; lean_object* v_r_996_; 
v_x_951__boxed_994_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_995_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_990_, v_x_991_, v_x_951__boxed_994_, v_x_993_);
lean_dec_ref(v_x_993_);
lean_dec_ref(v_x_991_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_997_, lean_object* v_x_998_, size_t v_x_999_, size_t v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_998_, v_x_999_, v_x_1000_, v_x_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
size_t v_x_962__boxed_1010_; size_t v_x_963__boxed_1011_; lean_object* v_res_1012_; 
v_x_962__boxed_1010_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_x_963__boxed_1011_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_res_1012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_1004_, v_x_1005_, v_x_962__boxed_1010_, v_x_963__boxed_1011_, v_x_1008_, v_x_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1013_, lean_object* v_keys_1014_, lean_object* v_vals_1015_, lean_object* v_heq_1016_, lean_object* v_i_1017_, lean_object* v_k_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_1014_, v_i_1017_, v_k_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1020_, lean_object* v_keys_1021_, lean_object* v_vals_1022_, lean_object* v_heq_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_1020_, v_keys_1021_, v_vals_1022_, v_heq_1023_, v_i_1024_, v_k_1025_);
lean_dec_ref(v_k_1025_);
lean_dec_ref(v_vals_1022_);
lean_dec_ref(v_keys_1021_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1028_, lean_object* v_n_1029_, lean_object* v_k_1030_, lean_object* v_v_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_1029_, v_k_1030_, v_v_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1033_, size_t v_depth_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_heq_1037_, lean_object* v_i_1038_, lean_object* v_entries_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_1034_, v_keys_1035_, v_vals_1036_, v_i_1038_, v_entries_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_depth_1042_, lean_object* v_keys_1043_, lean_object* v_vals_1044_, lean_object* v_heq_1045_, lean_object* v_i_1046_, lean_object* v_entries_1047_){
_start:
{
size_t v_depth_boxed_1048_; lean_object* v_res_1049_; 
v_depth_boxed_1048_ = lean_unbox_usize(v_depth_1042_);
lean_dec(v_depth_1042_);
v_res_1049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_1041_, v_depth_boxed_1048_, v_keys_1043_, v_vals_1044_, v_heq_1045_, v_i_1046_, v_entries_1047_);
lean_dec_ref(v_vals_1044_);
lean_dec_ref(v_keys_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_1051_, v_x_1052_, v_x_1053_, v_x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1057_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1058_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1057_, v___x_1056_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_1062_, lean_object* v_modIdx_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_1065_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1066_ = 0;
v___x_1067_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1064_, v___x_1065_, v_env_1062_, v_modIdx_1063_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_1068_, lean_object* v_modIdx_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_getExtraModUses(v_env_1068_, v_modIdx_1069_);
lean_dec(v_modIdx_1069_);
lean_dec_ref(v_env_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_1071_, lean_object* v_b_1072_){
_start:
{
if (lean_obj_tag(v_as_x27_1071_) == 0)
{
return v_b_1072_;
}
else
{
lean_object* v_head_1073_; lean_object* v_tail_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_head_1073_ = lean_ctor_get(v_as_x27_1071_, 0);
v_tail_1074_ = lean_ctor_get(v_as_x27_1071_, 1);
v___x_1075_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1076_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1077_ = lean_box(1);
v___x_1078_ = lean_box(0);
lean_inc_ref(v_b_1072_);
v___x_1079_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1075_, v___x_1076_, v_b_1072_, v___x_1077_, v___x_1078_);
v___x_1080_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_1079_, v_head_1073_);
lean_dec(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v_toEnvExtension_1081_; lean_object* v_asyncMode_1082_; lean_object* v___x_1083_; 
v_toEnvExtension_1081_ = lean_ctor_get(v___x_1076_, 0);
v_asyncMode_1082_ = lean_ctor_get(v_toEnvExtension_1081_, 2);
lean_inc(v_head_1073_);
v___x_1083_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1076_, v_b_1072_, v_head_1073_, v_asyncMode_1082_, v___x_1078_);
v_as_x27_1071_ = v_tail_1074_;
v_b_1072_ = v___x_1083_;
goto _start;
}
else
{
v_as_x27_1071_ = v_tail_1074_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_1086_, lean_object* v_b_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_1086_, v_b_1087_);
lean_dec(v_as_x27_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_1089_, lean_object* v_dest_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1091_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1092_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1093_ = lean_box(1);
v___x_1094_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1091_, v___x_1092_, v_src_1089_, v___x_1093_);
v___x_1095_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_1094_, v_dest_1090_);
lean_dec(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_1096_, lean_object* v_as_x27_1097_, lean_object* v_b_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_1097_, v_b_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_1101_, lean_object* v_as_x27_1102_, lean_object* v_b_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_1101_, v_as_x27_1102_, v_b_1103_, v_a_1104_);
lean_dec(v_as_x27_1102_);
lean_dec(v_as_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1106_, lean_object* v_entry_1107_, lean_object* v___x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v_toEnvExtension_1110_; lean_object* v_asyncMode_1111_; lean_object* v___x_1112_; 
v_toEnvExtension_1110_ = lean_ctor_get(v___x_1106_, 0);
v_asyncMode_1111_ = lean_ctor_get(v_toEnvExtension_1110_, 2);
lean_inc(v_asyncMode_1111_);
v___x_1112_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1106_, v_x_1109_, v_entry_1107_, v_asyncMode_1111_, v___x_1108_);
lean_dec(v_asyncMode_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0));
v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8));
v___x_1127_ = l_Lean_stringToMessageData(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_modifyEnv_1132_, lean_object* v___f_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_cls_1138_, lean_object* v_toBind_1139_, lean_object* v___f_1140_, lean_object* v_mod_1141_, lean_object* v_hint_1142_, uint8_t v_isMeta_1143_, uint8_t v_isExporting_1144_, uint8_t v_____do__lift_1145_){
_start:
{
lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1153_; lean_object* v___y_1154_; 
if (v_____do__lift_1145_ == 0)
{
lean_object* v___x_1166_; 
lean_dec(v_hint_1142_);
lean_dec(v_mod_1141_);
lean_dec(v___f_1140_);
lean_dec(v_toBind_1139_);
lean_dec(v_cls_1138_);
lean_dec(v_inst_1137_);
lean_dec_ref(v_inst_1136_);
lean_dec_ref(v_inst_1135_);
lean_dec_ref(v_inst_1134_);
v___x_1166_ = lean_apply_1(v_modifyEnv_1132_, v___f_1133_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___y_1169_; 
lean_dec_ref(v___f_1133_);
lean_dec(v_modifyEnv_1132_);
v___x_1167_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
if (v_isExporting_1144_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12));
v___y_1169_ = v___x_1176_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13));
v___y_1169_ = v___x_1177_;
goto v___jp_1168_;
}
v___jp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v___y_1169_);
v___x_1170_ = l_Lean_stringToMessageData(v___y_1169_);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1167_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
if (v_isMeta_1143_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10));
v___y_1153_ = v___x_1173_;
v___y_1154_ = v___x_1174_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11));
v___y_1153_ = v___x_1173_;
v___y_1154_ = v___x_1175_;
goto v___jp_1152_;
}
}
}
v___jp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___y_1147_);
lean_ctor_set(v___x_1149_, 1, v___y_1148_);
v___x_1150_ = l_Lean_addTrace___redArg(v_inst_1134_, v_inst_1135_, v_inst_1136_, v_inst_1137_, v_cls_1138_, v___x_1149_);
v___x_1151_ = lean_apply_4(v_toBind_1139_, lean_box(0), lean_box(0), v___x_1150_, v___f_1140_);
return v___x_1151_;
}
v___jp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
lean_inc_ref(v___y_1154_);
v___x_1155_ = l_Lean_stringToMessageData(v___y_1154_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___y_1153_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_MessageData_ofName(v_mod_1141_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_Name_isAnonymous(v_hint_1142_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
v___x_1163_ = l_Lean_MessageData_ofName(v_hint_1142_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___y_1147_ = v___x_1160_;
v___y_1148_ = v___x_1164_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1165_; 
lean_dec(v_hint_1142_);
v___x_1165_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
v___y_1147_ = v___x_1160_;
v___y_1148_ = v___x_1165_;
goto v___jp_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_modifyEnv_1178_, lean_object* v___f_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_cls_1184_, lean_object* v_toBind_1185_, lean_object* v___f_1186_, lean_object* v_mod_1187_, lean_object* v_hint_1188_, lean_object* v_isMeta_1189_, lean_object* v_isExporting_1190_, lean_object* v_____do__lift_1191_){
_start:
{
uint8_t v_isMeta_boxed_1192_; uint8_t v_isExporting_boxed_1193_; uint8_t v_____do__lift_963__boxed_1194_; lean_object* v_res_1195_; 
v_isMeta_boxed_1192_ = lean_unbox(v_isMeta_1189_);
v_isExporting_boxed_1193_ = lean_unbox(v_isExporting_1190_);
v_____do__lift_963__boxed_1194_ = lean_unbox(v_____do__lift_1191_);
v_res_1195_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_modifyEnv_1178_, v___f_1179_, v_inst_1180_, v_inst_1181_, v_inst_1182_, v_inst_1183_, v_cls_1184_, v_toBind_1185_, v___f_1186_, v_mod_1187_, v_hint_1188_, v_isMeta_boxed_1192_, v_isExporting_boxed_1193_, v_____do__lift_963__boxed_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v_entry_1199_, lean_object* v_inst_1200_, lean_object* v_toApplicative_1201_, lean_object* v_modifyEnv_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_toBind_1206_, lean_object* v_mod_1207_, lean_object* v_hint_1208_, uint8_t v_isMeta_1209_, uint8_t v_isExporting_1210_, lean_object* v_inst_1211_, lean_object* v_____do__lift_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1213_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1214_ = lean_box(1);
v___x_1215_ = lean_box(0);
v___x_1216_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1196_, v___x_1213_, v_____do__lift_1212_, v___x_1214_, v___x_1215_);
lean_inc_ref(v_entry_1199_);
v___x_1217_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1197_, v___x_1198_, v___x_1216_, v_entry_1199_);
if (v___x_1217_ == 0)
{
lean_object* v_getInheritedTraceOptions_1218_; lean_object* v_toPure_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v_cls_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_getInheritedTraceOptions_1218_ = lean_ctor_get(v_inst_1200_, 2);
lean_inc(v_getInheritedTraceOptions_1218_);
v_toPure_1219_ = lean_ctor_get(v_toApplicative_1201_, 1);
lean_inc(v_toPure_1219_);
lean_dec_ref(v_toApplicative_1201_);
v___f_1220_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1220_, 0, v___x_1213_);
lean_closure_set(v___f_1220_, 1, v_entry_1199_);
lean_closure_set(v___f_1220_, 2, v___x_1215_);
lean_inc_ref(v___f_1220_);
lean_inc(v_modifyEnv_1202_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1221_, 0, v_modifyEnv_1202_);
lean_closure_set(v___f_1221_, 1, v___f_1220_);
v_cls_1222_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1223_ = lean_box(v_isMeta_1209_);
v___x_1224_ = lean_box(v_isExporting_1210_);
lean_inc_n(v_toBind_1206_, 3);
v___f_1225_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1225_, 0, v_modifyEnv_1202_);
lean_closure_set(v___f_1225_, 1, v___f_1220_);
lean_closure_set(v___f_1225_, 2, v_inst_1203_);
lean_closure_set(v___f_1225_, 3, v_inst_1200_);
lean_closure_set(v___f_1225_, 4, v_inst_1204_);
lean_closure_set(v___f_1225_, 5, v_inst_1205_);
lean_closure_set(v___f_1225_, 6, v_cls_1222_);
lean_closure_set(v___f_1225_, 7, v_toBind_1206_);
lean_closure_set(v___f_1225_, 8, v___f_1221_);
lean_closure_set(v___f_1225_, 9, v_mod_1207_);
lean_closure_set(v___f_1225_, 10, v_hint_1208_);
lean_closure_set(v___f_1225_, 11, v___x_1223_);
lean_closure_set(v___f_1225_, 12, v___x_1224_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1226_, 0, v_toPure_1219_);
lean_closure_set(v___f_1226_, 1, v_cls_1222_);
lean_closure_set(v___f_1226_, 2, v_toBind_1206_);
lean_closure_set(v___f_1226_, 3, v_inst_1211_);
v___x_1227_ = lean_apply_4(v_toBind_1206_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1218_, v___f_1226_);
v___x_1228_ = lean_apply_4(v_toBind_1206_, lean_box(0), lean_box(0), v___x_1227_, v___f_1225_);
return v___x_1228_;
}
else
{
lean_object* v_toPure_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_inst_1211_);
lean_dec(v_hint_1208_);
lean_dec(v_mod_1207_);
lean_dec(v_toBind_1206_);
lean_dec(v_inst_1205_);
lean_dec_ref(v_inst_1204_);
lean_dec_ref(v_inst_1203_);
lean_dec(v_modifyEnv_1202_);
lean_dec_ref(v_inst_1200_);
lean_dec_ref(v_entry_1199_);
v_toPure_1229_ = lean_ctor_get(v_toApplicative_1201_, 1);
lean_inc(v_toPure_1229_);
lean_dec_ref(v_toApplicative_1201_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_apply_2(v_toPure_1229_, lean_box(0), v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1232_ = _args[0];
lean_object* v___x_1233_ = _args[1];
lean_object* v___x_1234_ = _args[2];
lean_object* v_entry_1235_ = _args[3];
lean_object* v_inst_1236_ = _args[4];
lean_object* v_toApplicative_1237_ = _args[5];
lean_object* v_modifyEnv_1238_ = _args[6];
lean_object* v_inst_1239_ = _args[7];
lean_object* v_inst_1240_ = _args[8];
lean_object* v_inst_1241_ = _args[9];
lean_object* v_toBind_1242_ = _args[10];
lean_object* v_mod_1243_ = _args[11];
lean_object* v_hint_1244_ = _args[12];
lean_object* v_isMeta_1245_ = _args[13];
lean_object* v_isExporting_1246_ = _args[14];
lean_object* v_inst_1247_ = _args[15];
lean_object* v_____do__lift_1248_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1249_; uint8_t v_isExporting_boxed_1250_; lean_object* v_res_1251_; 
v_isMeta_boxed_1249_ = lean_unbox(v_isMeta_1245_);
v_isExporting_boxed_1250_ = lean_unbox(v_isExporting_1246_);
v_res_1251_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v___x_1232_, v___x_1233_, v___x_1234_, v_entry_1235_, v_inst_1236_, v_toApplicative_1237_, v_modifyEnv_1238_, v_inst_1239_, v_inst_1240_, v_inst_1241_, v_toBind_1242_, v_mod_1243_, v_hint_1244_, v_isMeta_boxed_1249_, v_isExporting_boxed_1250_, v_inst_1247_, v_____do__lift_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v_mod_1252_, uint8_t v_isMeta_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v___x_1256_, lean_object* v_inst_1257_, lean_object* v_toApplicative_1258_, lean_object* v_modifyEnv_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_toBind_1263_, lean_object* v_hint_1264_, lean_object* v_inst_1265_, lean_object* v_getEnv_1266_, lean_object* v_____do__lift_1267_){
_start:
{
uint8_t v_isExporting_1268_; lean_object* v_entry_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; 
v_isExporting_1268_ = lean_ctor_get_uint8(v_____do__lift_1267_, sizeof(void*)*8);
lean_inc(v_mod_1252_);
v_entry_1269_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1269_, 0, v_mod_1252_);
lean_ctor_set_uint8(v_entry_1269_, sizeof(void*)*1, v_isExporting_1268_);
lean_ctor_set_uint8(v_entry_1269_, sizeof(void*)*1 + 1, v_isMeta_1253_);
v___x_1270_ = lean_box(v_isMeta_1253_);
v___x_1271_ = lean_box(v_isExporting_1268_);
lean_inc(v_toBind_1263_);
v___f_1272_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1272_, 0, v___x_1254_);
lean_closure_set(v___f_1272_, 1, v___x_1255_);
lean_closure_set(v___f_1272_, 2, v___x_1256_);
lean_closure_set(v___f_1272_, 3, v_entry_1269_);
lean_closure_set(v___f_1272_, 4, v_inst_1257_);
lean_closure_set(v___f_1272_, 5, v_toApplicative_1258_);
lean_closure_set(v___f_1272_, 6, v_modifyEnv_1259_);
lean_closure_set(v___f_1272_, 7, v_inst_1260_);
lean_closure_set(v___f_1272_, 8, v_inst_1261_);
lean_closure_set(v___f_1272_, 9, v_inst_1262_);
lean_closure_set(v___f_1272_, 10, v_toBind_1263_);
lean_closure_set(v___f_1272_, 11, v_mod_1252_);
lean_closure_set(v___f_1272_, 12, v_hint_1264_);
lean_closure_set(v___f_1272_, 13, v___x_1270_);
lean_closure_set(v___f_1272_, 14, v___x_1271_);
lean_closure_set(v___f_1272_, 15, v_inst_1265_);
v___x_1273_ = lean_apply_4(v_toBind_1263_, lean_box(0), lean_box(0), v_getEnv_1266_, v___f_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object* v_mod_1274_, lean_object* v_isMeta_1275_, lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v___x_1278_, lean_object* v_inst_1279_, lean_object* v_toApplicative_1280_, lean_object* v_modifyEnv_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_toBind_1285_, lean_object* v_hint_1286_, lean_object* v_inst_1287_, lean_object* v_getEnv_1288_, lean_object* v_____do__lift_1289_){
_start:
{
uint8_t v_isMeta_boxed_1290_; lean_object* v_res_1291_; 
v_isMeta_boxed_1290_ = lean_unbox(v_isMeta_1275_);
v_res_1291_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v_mod_1274_, v_isMeta_boxed_1290_, v___x_1276_, v___x_1277_, v___x_1278_, v_inst_1279_, v_toApplicative_1280_, v_modifyEnv_1281_, v_inst_1282_, v_inst_1283_, v_inst_1284_, v_toBind_1285_, v_hint_1286_, v_inst_1287_, v_getEnv_1288_, v_____do__lift_1289_);
lean_dec_ref(v_____do__lift_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_mod_1298_, uint8_t v_isMeta_1299_, lean_object* v_hint_1300_){
_start:
{
lean_object* v_toApplicative_1301_; lean_object* v_toBind_1302_; lean_object* v_getEnv_1303_; lean_object* v_modifyEnv_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; 
v_toApplicative_1301_ = lean_ctor_get(v_inst_1292_, 0);
lean_inc_ref(v_toApplicative_1301_);
v_toBind_1302_ = lean_ctor_get(v_inst_1292_, 1);
lean_inc_n(v_toBind_1302_, 2);
v_getEnv_1303_ = lean_ctor_get(v_inst_1293_, 0);
lean_inc_n(v_getEnv_1303_, 2);
v_modifyEnv_1304_ = lean_ctor_get(v_inst_1293_, 1);
lean_inc(v_modifyEnv_1304_);
lean_dec_ref(v_inst_1293_);
v___x_1305_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1306_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1307_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1308_ = lean_box(v_isMeta_1299_);
v___f_1309_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 16, 15);
lean_closure_set(v___f_1309_, 0, v_mod_1298_);
lean_closure_set(v___f_1309_, 1, v___x_1308_);
lean_closure_set(v___f_1309_, 2, v___x_1307_);
lean_closure_set(v___f_1309_, 3, v___x_1305_);
lean_closure_set(v___f_1309_, 4, v___x_1306_);
lean_closure_set(v___f_1309_, 5, v_inst_1294_);
lean_closure_set(v___f_1309_, 6, v_toApplicative_1301_);
lean_closure_set(v___f_1309_, 7, v_modifyEnv_1304_);
lean_closure_set(v___f_1309_, 8, v_inst_1292_);
lean_closure_set(v___f_1309_, 9, v_inst_1296_);
lean_closure_set(v___f_1309_, 10, v_inst_1297_);
lean_closure_set(v___f_1309_, 11, v_toBind_1302_);
lean_closure_set(v___f_1309_, 12, v_hint_1300_);
lean_closure_set(v___f_1309_, 13, v_inst_1295_);
lean_closure_set(v___f_1309_, 14, v_getEnv_1303_);
v___x_1310_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v_getEnv_1303_, v___f_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_mod_1317_, lean_object* v_isMeta_1318_, lean_object* v_hint_1319_){
_start:
{
uint8_t v_isMeta_boxed_1320_; lean_object* v_res_1321_; 
v_isMeta_boxed_1320_ = lean_unbox(v_isMeta_1318_);
v_res_1321_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1311_, v_inst_1312_, v_inst_1313_, v_inst_1314_, v_inst_1315_, v_inst_1316_, v_mod_1317_, v_isMeta_boxed_1320_, v_hint_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_mod_1329_, uint8_t v_isMeta_1330_, lean_object* v_hint_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_mod_1329_, v_isMeta_1330_, v_hint_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_mod_1340_, lean_object* v_isMeta_1341_, lean_object* v_hint_1342_){
_start:
{
uint8_t v_isMeta_boxed_1343_; lean_object* v_res_1344_; 
v_isMeta_boxed_1343_ = lean_unbox(v_isMeta_1341_);
v_res_1344_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1333_, v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_mod_1340_, v_isMeta_boxed_1343_, v_hint_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, uint8_t v_isMeta_1352_, lean_object* v_toApplicative_1353_, lean_object* v_____do__lift_1354_){
_start:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = l_Lean_Environment_mainModule(v_____do__lift_1354_);
v___x_1356_ = lean_name_eq(v_modName_1345_, v___x_1355_);
lean_dec(v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v_toApplicative_1353_);
v___x_1357_ = lean_box(0);
v___x_1358_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_inst_1351_, v_modName_1345_, v_isMeta_1352_, v___x_1357_);
return v___x_1358_;
}
else
{
lean_object* v_toPure_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec(v_inst_1351_);
lean_dec_ref(v_inst_1350_);
lean_dec(v_inst_1349_);
lean_dec_ref(v_inst_1348_);
lean_dec_ref(v_inst_1347_);
lean_dec_ref(v_inst_1346_);
lean_dec(v_modName_1345_);
v_toPure_1359_ = lean_ctor_get(v_toApplicative_1353_, 1);
lean_inc(v_toPure_1359_);
lean_dec_ref(v_toApplicative_1353_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_apply_2(v_toPure_1359_, lean_box(0), v___x_1360_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_isMeta_1369_, lean_object* v_toApplicative_1370_, lean_object* v_____do__lift_1371_){
_start:
{
uint8_t v_isMeta_boxed_1372_; lean_object* v_res_1373_; 
v_isMeta_boxed_1372_ = lean_unbox(v_isMeta_1369_);
v_res_1373_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1362_, v_inst_1363_, v_inst_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_inst_1368_, v_isMeta_boxed_1372_, v_toApplicative_1370_, v_____do__lift_1371_);
lean_dec_ref(v_____do__lift_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_modName_1380_, uint8_t v_isMeta_1381_){
_start:
{
lean_object* v_toApplicative_1382_; lean_object* v_toBind_1383_; lean_object* v_getEnv_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v_toApplicative_1382_ = lean_ctor_get(v_inst_1374_, 0);
lean_inc_ref(v_toApplicative_1382_);
v_toBind_1383_ = lean_ctor_get(v_inst_1374_, 1);
lean_inc(v_toBind_1383_);
v_getEnv_1384_ = lean_ctor_get(v_inst_1375_, 0);
lean_inc(v_getEnv_1384_);
v___x_1385_ = lean_box(v_isMeta_1381_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1386_, 0, v_modName_1380_);
lean_closure_set(v___f_1386_, 1, v_inst_1374_);
lean_closure_set(v___f_1386_, 2, v_inst_1375_);
lean_closure_set(v___f_1386_, 3, v_inst_1376_);
lean_closure_set(v___f_1386_, 4, v_inst_1377_);
lean_closure_set(v___f_1386_, 5, v_inst_1378_);
lean_closure_set(v___f_1386_, 6, v_inst_1379_);
lean_closure_set(v___f_1386_, 7, v___x_1385_);
lean_closure_set(v___f_1386_, 8, v_toApplicative_1382_);
v___x_1387_ = lean_apply_4(v_toBind_1383_, lean_box(0), lean_box(0), v_getEnv_1384_, v___f_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_modName_1394_, lean_object* v_isMeta_1395_){
_start:
{
uint8_t v_isMeta_boxed_1396_; lean_object* v_res_1397_; 
v_isMeta_boxed_1396_ = lean_unbox(v_isMeta_1395_);
v_res_1397_ = l_Lean_recordExtraModUse___redArg(v_inst_1388_, v_inst_1389_, v_inst_1390_, v_inst_1391_, v_inst_1392_, v_inst_1393_, v_modName_1394_, v_isMeta_boxed_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_modName_1405_, uint8_t v_isMeta_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_recordExtraModUse___redArg(v_inst_1399_, v_inst_1400_, v_inst_1401_, v_inst_1402_, v_inst_1403_, v_inst_1404_, v_modName_1405_, v_isMeta_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_modName_1415_, lean_object* v_isMeta_1416_){
_start:
{
uint8_t v_isMeta_boxed_1417_; lean_object* v_res_1418_; 
v_isMeta_boxed_1417_ = lean_unbox(v_isMeta_1416_);
v_res_1418_ = l_Lean_recordExtraModUse(v_m_1408_, v_inst_1409_, v_inst_1410_, v_inst_1411_, v_inst_1412_, v_inst_1413_, v_inst_1414_, v_modName_1415_, v_isMeta_boxed_1417_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1419_, lean_object* v_____s_1420_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_apply_2(v_toPure_1419_, lean_box(0), v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1423_, lean_object* v_toPure_1424_, lean_object* v_r_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1423_);
v___x_1427_ = lean_apply_2(v_toPure_1424_, lean_box(0), v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1428_, lean_object* v___x_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_declName_1436_, lean_object* v_toBind_1437_, lean_object* v___f_1438_, lean_object* v_a_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v_modules_1443_; lean_object* v___x_1444_; lean_object* v_toImport_1445_; lean_object* v_module_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1442_ = l_Lean_Environment_header(v_env_1428_);
v_modules_1443_ = lean_ctor_get(v___x_1442_, 3);
lean_inc_ref(v_modules_1443_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = lean_array_get(v___x_1429_, v_modules_1443_, v_a_1439_);
lean_dec_ref(v_modules_1443_);
v_toImport_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc_ref(v_toImport_1445_);
lean_dec(v___x_1444_);
v_module_1446_ = lean_ctor_get(v_toImport_1445_, 0);
lean_inc(v_module_1446_);
lean_dec_ref(v_toImport_1445_);
v___x_1447_ = 0;
v___x_1448_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1430_, v_inst_1431_, v_inst_1432_, v_inst_1433_, v_inst_1434_, v_inst_1435_, v_module_1446_, v___x_1447_, v_declName_1436_);
v___x_1449_ = lean_apply_4(v_toBind_1437_, lean_box(0), lean_box(0), v___x_1448_, v___f_1438_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1450_, lean_object* v___x_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_declName_1458_, lean_object* v_toBind_1459_, lean_object* v___f_1460_, lean_object* v_a_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1450_, v___x_1451_, v_inst_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_inst_1456_, v_inst_1457_, v_declName_1458_, v_toBind_1459_, v___f_1460_, v_a_1461_, v_x_1462_, v___y_1463_);
lean_dec(v_a_1461_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_env_1450_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1465_, lean_object* v_env_1466_, lean_object* v___x_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_declName_1474_, lean_object* v_toBind_1475_, lean_object* v___f_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v_____r_1480_){
_start:
{
lean_object* v___y_1482_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1490_ = l_Lean_indirectModUseExt;
v___x_1491_ = lean_box(1);
v___x_1492_ = lean_box(0);
lean_inc_ref(v_env_1466_);
v___x_1493_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1477_, v___x_1490_, v_env_1466_, v___x_1491_, v___x_1492_);
lean_inc(v_declName_1474_);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1478_, v___x_1479_, v___x_1493_, v_declName_1474_);
lean_dec(v___x_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___lam__0___closed__0));
v___y_1482_ = v___x_1495_;
goto v___jp_1481_;
}
else
{
lean_object* v_val_1496_; 
v_val_1496_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v___x_1494_, 1);
v___y_1482_ = v_val_1496_;
goto v___jp_1481_;
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1483_ = lean_box(0);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1484_, 0, v___x_1483_);
lean_closure_set(v___f_1484_, 1, v_toPure_1465_);
lean_inc(v_toBind_1475_);
lean_inc_ref(v_inst_1468_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1485_, 0, v_env_1466_);
lean_closure_set(v___f_1485_, 1, v___x_1467_);
lean_closure_set(v___f_1485_, 2, v_inst_1468_);
lean_closure_set(v___f_1485_, 3, v_inst_1469_);
lean_closure_set(v___f_1485_, 4, v_inst_1470_);
lean_closure_set(v___f_1485_, 5, v_inst_1471_);
lean_closure_set(v___f_1485_, 6, v_inst_1472_);
lean_closure_set(v___f_1485_, 7, v_inst_1473_);
lean_closure_set(v___f_1485_, 8, v_declName_1474_);
lean_closure_set(v___f_1485_, 9, v_toBind_1475_);
lean_closure_set(v___f_1485_, 10, v___f_1484_);
v_sz_1486_ = lean_array_size(v___y_1482_);
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1468_, v___y_1482_, v___f_1485_, v_sz_1486_, v___x_1487_, v___x_1483_);
v___x_1489_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v___x_1488_, v___f_1476_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_declName_1504_, lean_object* v_toBind_1505_, lean_object* v___f_1506_, uint8_t v_isMeta_1507_, lean_object* v_____do__lift_1508_){
_start:
{
uint8_t v___y_1510_; 
if (v_isMeta_1507_ == 0)
{
lean_dec_ref(v_____do__lift_1508_);
v___y_1510_ = v_isMeta_1507_;
goto v___jp_1509_;
}
else
{
uint8_t v___x_1515_; 
lean_inc(v_declName_1504_);
v___x_1515_ = l_Lean_isMarkedMeta(v_____do__lift_1508_, v_declName_1504_);
if (v___x_1515_ == 0)
{
v___y_1510_ = v_isMeta_1507_;
goto v___jp_1509_;
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = 0;
v___y_1510_ = v___x_1516_;
goto v___jp_1509_;
}
}
v___jp_1509_:
{
lean_object* v_toImport_1511_; lean_object* v_module_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_toImport_1511_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_toImport_1511_);
lean_dec_ref(v___x_1497_);
v_module_1512_ = lean_ctor_get(v_toImport_1511_, 0);
lean_inc(v_module_1512_);
lean_dec_ref(v_toImport_1511_);
v___x_1513_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1498_, v_inst_1499_, v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_module_1512_, v___y_1510_, v_declName_1504_);
v___x_1514_ = lean_apply_4(v_toBind_1505_, lean_box(0), lean_box(0), v___x_1513_, v___f_1506_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_declName_1524_, lean_object* v_toBind_1525_, lean_object* v___f_1526_, lean_object* v_isMeta_1527_, lean_object* v_____do__lift_1528_){
_start:
{
uint8_t v_isMeta_boxed_1529_; lean_object* v_res_1530_; 
v_isMeta_boxed_1529_ = lean_unbox(v_isMeta_1527_);
v_res_1530_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_declName_1524_, v_toBind_1525_, v___f_1526_, v_isMeta_boxed_1529_, v_____do__lift_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1531_, lean_object* v_declName_1532_, lean_object* v___x_1533_, lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_toBind_1540_, lean_object* v___f_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, uint8_t v_isMeta_1545_, lean_object* v_getEnv_1546_, lean_object* v_env_1547_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1547_, v_declName_1532_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_dec_ref(v_env_1547_);
lean_dec(v_getEnv_1546_);
lean_dec_ref(v___x_1544_);
lean_dec_ref(v___x_1543_);
lean_dec_ref(v___x_1542_);
lean_dec(v___f_1541_);
lean_dec(v_toBind_1540_);
lean_dec(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
lean_dec(v_inst_1537_);
lean_dec_ref(v_inst_1536_);
lean_dec_ref(v_inst_1535_);
lean_dec_ref(v_inst_1534_);
lean_dec_ref(v___x_1533_);
lean_dec(v_declName_1532_);
goto v___jp_1548_;
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1553_; lean_object* v_modules_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = l_Lean_Environment_header(v_env_1547_);
v_modules_1554_ = lean_ctor_get(v___x_1553_, 3);
lean_inc_ref(v_modules_1554_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = lean_array_get_size(v_modules_1554_);
v___x_1556_ = lean_nat_dec_lt(v_val_1552_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v_modules_1554_);
lean_dec(v_val_1552_);
lean_dec_ref(v_env_1547_);
lean_dec(v_getEnv_1546_);
lean_dec_ref(v___x_1544_);
lean_dec_ref(v___x_1543_);
lean_dec_ref(v___x_1542_);
lean_dec(v___f_1541_);
lean_dec(v_toBind_1540_);
lean_dec(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
lean_dec(v_inst_1537_);
lean_dec_ref(v_inst_1536_);
lean_dec_ref(v_inst_1535_);
lean_dec_ref(v_inst_1534_);
lean_dec_ref(v___x_1533_);
lean_dec(v_declName_1532_);
goto v___jp_1548_;
}
else
{
lean_object* v___f_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
lean_inc_n(v_toBind_1540_, 2);
lean_inc(v_declName_1532_);
lean_inc(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
lean_inc(v_inst_1537_);
lean_inc_ref(v_inst_1536_);
lean_inc_ref(v_inst_1535_);
lean_inc_ref(v_inst_1534_);
v___f_1557_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1557_, 0, v_toPure_1531_);
lean_closure_set(v___f_1557_, 1, v_env_1547_);
lean_closure_set(v___f_1557_, 2, v___x_1533_);
lean_closure_set(v___f_1557_, 3, v_inst_1534_);
lean_closure_set(v___f_1557_, 4, v_inst_1535_);
lean_closure_set(v___f_1557_, 5, v_inst_1536_);
lean_closure_set(v___f_1557_, 6, v_inst_1537_);
lean_closure_set(v___f_1557_, 7, v_inst_1538_);
lean_closure_set(v___f_1557_, 8, v_inst_1539_);
lean_closure_set(v___f_1557_, 9, v_declName_1532_);
lean_closure_set(v___f_1557_, 10, v_toBind_1540_);
lean_closure_set(v___f_1557_, 11, v___f_1541_);
lean_closure_set(v___f_1557_, 12, v___x_1542_);
lean_closure_set(v___f_1557_, 13, v___x_1543_);
lean_closure_set(v___f_1557_, 14, v___x_1544_);
v___x_1558_ = lean_array_fget(v_modules_1554_, v_val_1552_);
lean_dec(v_val_1552_);
lean_dec_ref(v_modules_1554_);
v___x_1559_ = lean_box(v_isMeta_1545_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1560_, 0, v___x_1558_);
lean_closure_set(v___f_1560_, 1, v_inst_1534_);
lean_closure_set(v___f_1560_, 2, v_inst_1535_);
lean_closure_set(v___f_1560_, 3, v_inst_1536_);
lean_closure_set(v___f_1560_, 4, v_inst_1537_);
lean_closure_set(v___f_1560_, 5, v_inst_1538_);
lean_closure_set(v___f_1560_, 6, v_inst_1539_);
lean_closure_set(v___f_1560_, 7, v_declName_1532_);
lean_closure_set(v___f_1560_, 8, v_toBind_1540_);
lean_closure_set(v___f_1560_, 9, v___f_1557_);
lean_closure_set(v___f_1560_, 10, v___x_1559_);
v___x_1561_ = lean_apply_4(v_toBind_1540_, lean_box(0), lean_box(0), v_getEnv_1546_, v___f_1560_);
return v___x_1561_;
}
}
v___jp_1548_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_apply_2(v_toPure_1531_, lean_box(0), v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1562_ = _args[0];
lean_object* v_declName_1563_ = _args[1];
lean_object* v___x_1564_ = _args[2];
lean_object* v_inst_1565_ = _args[3];
lean_object* v_inst_1566_ = _args[4];
lean_object* v_inst_1567_ = _args[5];
lean_object* v_inst_1568_ = _args[6];
lean_object* v_inst_1569_ = _args[7];
lean_object* v_inst_1570_ = _args[8];
lean_object* v_toBind_1571_ = _args[9];
lean_object* v___f_1572_ = _args[10];
lean_object* v___x_1573_ = _args[11];
lean_object* v___x_1574_ = _args[12];
lean_object* v___x_1575_ = _args[13];
lean_object* v_isMeta_1576_ = _args[14];
lean_object* v_getEnv_1577_ = _args[15];
lean_object* v_env_1578_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1579_; lean_object* v_res_1580_; 
v_isMeta_boxed_1579_ = lean_unbox(v_isMeta_1576_);
v_res_1580_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1562_, v_declName_1563_, v___x_1564_, v_inst_1565_, v_inst_1566_, v_inst_1567_, v_inst_1568_, v_inst_1569_, v_inst_1570_, v_toBind_1571_, v___f_1572_, v___x_1573_, v___x_1574_, v___x_1575_, v_isMeta_boxed_1579_, v_getEnv_1577_, v_env_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_declName_1587_, uint8_t v_isMeta_1588_){
_start:
{
lean_object* v_toApplicative_1589_; lean_object* v_toBind_1590_; lean_object* v_getEnv_1591_; lean_object* v_toPure_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; 
v_toApplicative_1589_ = lean_ctor_get(v_inst_1581_, 0);
v_toBind_1590_ = lean_ctor_get(v_inst_1581_, 1);
lean_inc_n(v_toBind_1590_, 2);
v_getEnv_1591_ = lean_ctor_get(v_inst_1582_, 0);
lean_inc_n(v_getEnv_1591_, 2);
v_toPure_1592_ = lean_ctor_get(v_toApplicative_1589_, 1);
lean_inc_n(v_toPure_1592_, 2);
v___x_1593_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1594_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1595_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1596_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1597_, 0, v_toPure_1592_);
v___x_1598_ = lean_box(v_isMeta_1588_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1599_, 0, v_toPure_1592_);
lean_closure_set(v___f_1599_, 1, v_declName_1587_);
lean_closure_set(v___f_1599_, 2, v___x_1596_);
lean_closure_set(v___f_1599_, 3, v_inst_1581_);
lean_closure_set(v___f_1599_, 4, v_inst_1582_);
lean_closure_set(v___f_1599_, 5, v_inst_1583_);
lean_closure_set(v___f_1599_, 6, v_inst_1584_);
lean_closure_set(v___f_1599_, 7, v_inst_1585_);
lean_closure_set(v___f_1599_, 8, v_inst_1586_);
lean_closure_set(v___f_1599_, 9, v_toBind_1590_);
lean_closure_set(v___f_1599_, 10, v___f_1597_);
lean_closure_set(v___f_1599_, 11, v___x_1595_);
lean_closure_set(v___f_1599_, 12, v___x_1593_);
lean_closure_set(v___f_1599_, 13, v___x_1594_);
lean_closure_set(v___f_1599_, 14, v___x_1598_);
lean_closure_set(v___f_1599_, 15, v_getEnv_1591_);
v___x_1600_ = lean_apply_4(v_toBind_1590_, lean_box(0), lean_box(0), v_getEnv_1591_, v___f_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_declName_1607_, lean_object* v_isMeta_1608_){
_start:
{
uint8_t v_isMeta_boxed_1609_; lean_object* v_res_1610_; 
v_isMeta_boxed_1609_ = lean_unbox(v_isMeta_1608_);
v_res_1610_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1601_, v_inst_1602_, v_inst_1603_, v_inst_1604_, v_inst_1605_, v_inst_1606_, v_declName_1607_, v_isMeta_boxed_1609_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_declName_1618_, uint8_t v_isMeta_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_inst_1616_, v_inst_1617_, v_declName_1618_, v_isMeta_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_declName_1628_, lean_object* v_isMeta_1629_){
_start:
{
uint8_t v_isMeta_boxed_1630_; lean_object* v_res_1631_; 
v_isMeta_boxed_1630_ = lean_unbox(v_isMeta_1629_);
v_res_1631_ = l_Lean_recordExtraModUseFromDecl(v_m_1621_, v_inst_1622_, v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_declName_1628_, v_isMeta_boxed_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1632_, lean_object* v_e_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_box(0);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_box(0);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1637_);
lean_dec_ref(v_x_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_array_mk(v_es_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1657_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1659_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1663_, lean_object* v_modIdx_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1665_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1666_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1667_ = 0;
v___x_1668_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1665_, v___x_1666_, v_env_1663_, v_modIdx_1664_, v___x_1667_);
v___x_1669_ = lean_array_get_size(v___x_1668_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_nat_dec_eq(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = 1;
return v___x_1672_;
}
else
{
uint8_t v___x_1673_; 
v___x_1673_ = 0;
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1674_, lean_object* v_modIdx_1675_){
_start:
{
uint8_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l_Lean_isExtraRevModUse(v_env_1674_, v_modIdx_1675_);
lean_dec(v_modIdx_1675_);
lean_dec_ref(v_env_1674_);
v_r_1677_ = lean_box(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v_toEnvExtension_1680_; lean_object* v_asyncMode_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_toEnvExtension_1680_ = lean_ctor_get(v___x_1678_, 0);
v_asyncMode_1681_ = lean_ctor_get(v_toEnvExtension_1680_, 2);
lean_inc(v_asyncMode_1681_);
v___x_1682_ = lean_box(0);
v___x_1683_ = lean_box(0);
v___x_1684_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1678_, v_x_1679_, v___x_1682_, v_asyncMode_1681_, v___x_1683_);
lean_dec(v_asyncMode_1681_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0));
v___x_1687_ = l_Lean_stringToMessageData(v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v_modifyEnv_1688_, lean_object* v___f_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_cls_1694_, lean_object* v_toBind_1695_, lean_object* v___f_1696_, uint8_t v_____do__lift_1697_){
_start:
{
if (v_____do__lift_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v___f_1696_);
lean_dec(v_toBind_1695_);
lean_dec(v_cls_1694_);
lean_dec(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
lean_dec_ref(v_inst_1691_);
lean_dec_ref(v_inst_1690_);
v___x_1698_ = lean_apply_1(v_modifyEnv_1688_, v___f_1689_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec_ref(v___f_1689_);
lean_dec(v_modifyEnv_1688_);
v___x_1699_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1);
v___x_1700_ = l_Lean_addTrace___redArg(v_inst_1690_, v_inst_1691_, v_inst_1692_, v_inst_1693_, v_cls_1694_, v___x_1699_);
v___x_1701_ = lean_apply_4(v_toBind_1695_, lean_box(0), lean_box(0), v___x_1700_, v___f_1696_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object* v_modifyEnv_1702_, lean_object* v___f_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_cls_1708_, lean_object* v_toBind_1709_, lean_object* v___f_1710_, lean_object* v_____do__lift_1711_){
_start:
{
uint8_t v_____do__lift_328__boxed_1712_; lean_object* v_res_1713_; 
v_____do__lift_328__boxed_1712_ = lean_unbox(v_____do__lift_1711_);
v_res_1713_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(v_modifyEnv_1702_, v___f_1703_, v_inst_1704_, v_inst_1705_, v_inst_1706_, v_inst_1707_, v_cls_1708_, v_toBind_1709_, v___f_1710_, v_____do__lift_328__boxed_1712_);
return v_res_1713_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___f_1715_; 
v___x_1714_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1715_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1715_, 0, v___x_1714_);
return v___f_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v___x_1716_, lean_object* v_toApplicative_1717_, lean_object* v_inst_1718_, lean_object* v_modifyEnv_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_toBind_1723_, lean_object* v_inst_1724_, lean_object* v_____do__lift_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1726_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1727_ = lean_box(1);
v___x_1728_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1716_, v___x_1726_, v_____do__lift_1725_, v___x_1727_);
v___x_1729_ = l_List_isEmpty___redArg(v___x_1728_);
lean_dec(v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v_toPure_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_inst_1724_);
lean_dec(v_toBind_1723_);
lean_dec(v_inst_1722_);
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1720_);
lean_dec(v_modifyEnv_1719_);
lean_dec_ref(v_inst_1718_);
v_toPure_1730_ = lean_ctor_get(v_toApplicative_1717_, 1);
lean_inc(v_toPure_1730_);
lean_dec_ref(v_toApplicative_1717_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_apply_2(v_toPure_1730_, lean_box(0), v___x_1731_);
return v___x_1732_;
}
else
{
lean_object* v_getInheritedTraceOptions_1733_; lean_object* v_toPure_1734_; lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v_cls_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_getInheritedTraceOptions_1733_ = lean_ctor_get(v_inst_1718_, 2);
lean_inc(v_getInheritedTraceOptions_1733_);
v_toPure_1734_ = lean_ctor_get(v_toApplicative_1717_, 1);
lean_inc(v_toPure_1734_);
lean_dec_ref(v_toApplicative_1717_);
v___f_1735_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0);
lean_inc(v_modifyEnv_1719_);
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1736_, 0, v_modifyEnv_1719_);
lean_closure_set(v___f_1736_, 1, v___f_1735_);
v_cls_1737_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1723_, 3);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1738_, 0, v_modifyEnv_1719_);
lean_closure_set(v___f_1738_, 1, v___f_1735_);
lean_closure_set(v___f_1738_, 2, v_inst_1720_);
lean_closure_set(v___f_1738_, 3, v_inst_1718_);
lean_closure_set(v___f_1738_, 4, v_inst_1721_);
lean_closure_set(v___f_1738_, 5, v_inst_1722_);
lean_closure_set(v___f_1738_, 6, v_cls_1737_);
lean_closure_set(v___f_1738_, 7, v_toBind_1723_);
lean_closure_set(v___f_1738_, 8, v___f_1736_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1739_, 0, v_toPure_1734_);
lean_closure_set(v___f_1739_, 1, v_cls_1737_);
lean_closure_set(v___f_1739_, 2, v_toBind_1723_);
lean_closure_set(v___f_1739_, 3, v_inst_1724_);
v___x_1740_ = lean_apply_4(v_toBind_1723_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1733_, v___f_1739_);
v___x_1741_ = lean_apply_4(v_toBind_1723_, lean_box(0), lean_box(0), v___x_1740_, v___f_1738_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_){
_start:
{
lean_object* v_toApplicative_1748_; lean_object* v_toBind_1749_; lean_object* v_getEnv_1750_; lean_object* v_modifyEnv_1751_; lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; 
v_toApplicative_1748_ = lean_ctor_get(v_inst_1742_, 0);
lean_inc_ref(v_toApplicative_1748_);
v_toBind_1749_ = lean_ctor_get(v_inst_1742_, 1);
lean_inc_n(v_toBind_1749_, 2);
v_getEnv_1750_ = lean_ctor_get(v_inst_1743_, 0);
lean_inc(v_getEnv_1750_);
v_modifyEnv_1751_ = lean_ctor_get(v_inst_1743_, 1);
lean_inc(v_modifyEnv_1751_);
lean_dec_ref(v_inst_1743_);
v___x_1752_ = lean_box(0);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4), 10, 9);
lean_closure_set(v___f_1753_, 0, v___x_1752_);
lean_closure_set(v___f_1753_, 1, v_toApplicative_1748_);
lean_closure_set(v___f_1753_, 2, v_inst_1744_);
lean_closure_set(v___f_1753_, 3, v_modifyEnv_1751_);
lean_closure_set(v___f_1753_, 4, v_inst_1742_);
lean_closure_set(v___f_1753_, 5, v_inst_1746_);
lean_closure_set(v___f_1753_, 6, v_inst_1747_);
lean_closure_set(v___f_1753_, 7, v_toBind_1749_);
lean_closure_set(v___f_1753_, 8, v_inst_1745_);
v___x_1754_ = lean_apply_4(v_toBind_1749_, lean_box(0), lean_box(0), v_getEnv_1750_, v___f_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1756_, v_inst_1757_, v_inst_1758_, v_inst_1759_, v_inst_1760_, v_inst_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_unsigned_to_nat(4259277863u);
v___x_1778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1779_ = l_Lean_Name_num___override(v___x_1778_, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1782_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1783_ = l_Lean_Name_str___override(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1786_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1787_ = l_Lean_Name_str___override(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_unsigned_to_nat(2u);
v___x_1789_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1790_ = l_Lean_Name_num___override(v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1792_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1793_ = 0;
v___x_1794_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1795_ = l_Lean_registerTraceClass(v___x_1792_, v___x_1793_, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1797_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
