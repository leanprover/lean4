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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
return v_x_22_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_52_; 
v_key_24_ = lean_ctor_get(v_x_23_, 0);
v_value_25_ = lean_ctor_get(v_x_23_, 1);
v_tail_26_ = lean_ctor_get(v_x_23_, 2);
v_isSharedCheck_52_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_52_ == 0)
{
v___x_28_ = v_x_23_;
v_isShared_29_ = v_isSharedCheck_52_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_value_25_);
lean_inc(v_key_24_);
lean_dec(v_x_23_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_52_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; uint64_t v___y_32_; 
v___x_30_ = lean_array_get_size(v_x_22_);
if (lean_obj_tag(v_key_24_) == 0)
{
uint64_t v___x_50_; 
v___x_50_ = 1723ULL;
v___y_32_ = v___x_50_;
goto v___jp_31_;
}
else
{
uint64_t v_hash_51_; 
v_hash_51_ = lean_ctor_get_uint64(v_key_24_, sizeof(void*)*2);
v___y_32_ = v_hash_51_;
goto v___jp_31_;
}
v___jp_31_:
{
uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v_fold_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_33_ = 32ULL;
v___x_34_ = lean_uint64_shift_right(v___y_32_, v___x_33_);
v_fold_35_ = lean_uint64_xor(v___y_32_, v___x_34_);
v___x_36_ = 16ULL;
v___x_37_ = lean_uint64_shift_right(v_fold_35_, v___x_36_);
v___x_38_ = lean_uint64_xor(v_fold_35_, v___x_37_);
v___x_39_ = lean_uint64_to_usize(v___x_38_);
v___x_40_ = lean_usize_of_nat(v___x_30_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_sub(v___x_40_, v___x_41_);
v___x_43_ = lean_usize_land(v___x_39_, v___x_42_);
v___x_44_ = lean_array_uget_borrowed(v_x_22_, v___x_43_);
lean_inc(v___x_44_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 2, v___x_44_);
v___x_46_ = v___x_28_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_key_24_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_value_25_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v___x_44_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
v___x_47_ = lean_array_uset(v_x_22_, v___x_43_, v___x_46_);
v_x_22_ = v___x_47_;
v_x_23_ = v_tail_26_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_53_, lean_object* v_source_54_, lean_object* v_target_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = lean_array_get_size(v_source_54_);
v___x_57_ = lean_nat_dec_lt(v_i_53_, v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v_source_54_);
lean_dec(v_i_53_);
return v_target_55_;
}
else
{
lean_object* v_es_58_; lean_object* v___x_59_; lean_object* v_source_60_; lean_object* v_target_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_es_58_ = lean_array_fget(v_source_54_, v_i_53_);
v___x_59_ = lean_box(0);
v_source_60_ = lean_array_fset(v_source_54_, v_i_53_, v___x_59_);
v_target_61_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_target_55_, v_es_58_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_i_53_, v___x_62_);
lean_dec(v_i_53_);
v_i_53_ = v___x_63_;
v_source_54_ = v_source_60_;
v_target_55_ = v_target_61_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_nbuckets_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_66_ = lean_array_get_size(v_data_65_);
v___x_67_ = lean_unsigned_to_nat(2u);
v_nbuckets_68_ = lean_nat_mul(v___x_66_, v___x_67_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_box(0);
v___x_71_ = lean_mk_array(v_nbuckets_68_, v___x_70_);
v___x_72_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_69_, v_data_65_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object* v_val_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___y_78_; 
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_78_ = v___x_81_;
goto v___jp_77_;
}
else
{
lean_object* v_val_82_; 
v_val_82_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v_x_76_, 1);
v___y_78_ = v_val_82_;
goto v___jp_77_;
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_array_push(v___y_78_, v_val_75_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_val_83_, lean_object* v_a_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_val_88_; lean_object* v___x_89_; 
v___x_86_ = lean_box(0);
v___x_87_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_83_, v___x_86_);
v_val_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_val_88_);
lean_dec(v___x_87_);
v___x_89_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_89_, 0, v_a_84_);
lean_ctor_set(v___x_89_, 1, v_val_88_);
lean_ctor_set(v___x_89_, 2, v_x_85_);
return v___x_89_;
}
else
{
lean_object* v_key_90_; lean_object* v_value_91_; lean_object* v_tail_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_107_; 
v_key_90_ = lean_ctor_get(v_x_85_, 0);
v_value_91_ = lean_ctor_get(v_x_85_, 1);
v_tail_92_ = lean_ctor_get(v_x_85_, 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_107_ == 0)
{
v___x_94_ = v_x_85_;
v_isShared_95_ = v_isSharedCheck_107_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_tail_92_);
lean_inc(v_value_91_);
lean_inc(v_key_90_);
lean_dec(v_x_85_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_107_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
uint8_t v___x_96_; 
v___x_96_ = lean_name_eq(v_key_90_, v_a_84_);
if (v___x_96_ == 0)
{
lean_object* v_tail_97_; lean_object* v___x_99_; 
v_tail_97_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_83_, v_a_84_, v_tail_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 2, v_tail_97_);
v___x_99_ = v___x_94_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_key_90_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_value_91_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_tail_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_val_103_; lean_object* v___x_105_; 
lean_dec(v_key_90_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_value_91_);
v___x_102_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_83_, v___x_101_);
v_val_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_val_103_);
lean_dec(v___x_102_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_val_103_);
lean_ctor_set(v___x_94_, 0, v_a_84_);
v___x_105_ = v___x_94_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_84_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_val_103_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_tail_92_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
else
{
lean_object* v_key_111_; lean_object* v_tail_112_; uint8_t v___x_113_; 
v_key_111_ = lean_ctor_get(v_x_109_, 0);
v_tail_112_ = lean_ctor_get(v_x_109_, 2);
v___x_113_ = lean_name_eq(v_key_111_, v_a_108_);
if (v___x_113_ == 0)
{
v_x_109_ = v_tail_112_;
goto _start;
}
else
{
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec(v_a_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_val_119_, lean_object* v_m_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___y_123_; size_t v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v_size_129_; lean_object* v_buckets_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_177_; 
v_size_129_ = lean_ctor_get(v_m_120_, 0);
v_buckets_130_ = lean_ctor_get(v_m_120_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_m_120_);
if (v_isSharedCheck_177_ == 0)
{
v___x_132_ = v_m_120_;
v_isShared_133_ = v_isSharedCheck_177_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_buckets_130_);
lean_inc(v_size_129_);
lean_dec(v_m_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_177_;
goto v_resetjp_131_;
}
v___jp_122_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_array_uset(v___y_123_, v___y_124_, v___y_125_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___y_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; uint64_t v___y_136_; 
v___x_134_ = lean_array_get_size(v_buckets_130_);
if (lean_obj_tag(v_a_121_) == 0)
{
uint64_t v___x_175_; 
v___x_175_ = 1723ULL;
v___y_136_ = v___x_175_;
goto v___jp_135_;
}
else
{
uint64_t v_hash_176_; 
v_hash_176_ = lean_ctor_get_uint64(v_a_121_, sizeof(void*)*2);
v___y_136_ = v_hash_176_;
goto v___jp_135_;
}
v___jp_135_:
{
uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v_fold_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; lean_object* v_bkt_148_; uint8_t v___x_149_; 
v___x_137_ = 32ULL;
v___x_138_ = lean_uint64_shift_right(v___y_136_, v___x_137_);
v_fold_139_ = lean_uint64_xor(v___y_136_, v___x_138_);
v___x_140_ = 16ULL;
v___x_141_ = lean_uint64_shift_right(v_fold_139_, v___x_140_);
v___x_142_ = lean_uint64_xor(v_fold_139_, v___x_141_);
v___x_143_ = lean_uint64_to_usize(v___x_142_);
v___x_144_ = lean_usize_of_nat(v___x_134_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_sub(v___x_144_, v___x_145_);
v___x_147_ = lean_usize_land(v___x_143_, v___x_146_);
v_bkt_148_ = lean_array_uget_borrowed(v_buckets_130_, v___x_147_);
v___x_149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_121_, v_bkt_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_size_x27_153_; lean_object* v___x_154_; lean_object* v_buckets_x27_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_150_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___x_151_ = lean_array_push(v___x_150_, v_val_119_);
v___x_152_ = lean_unsigned_to_nat(1u);
v_size_x27_153_ = lean_nat_add(v_size_129_, v___x_152_);
lean_dec(v_size_129_);
lean_inc(v_bkt_148_);
v___x_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_154_, 0, v_a_121_);
lean_ctor_set(v___x_154_, 1, v___x_151_);
lean_ctor_set(v___x_154_, 2, v_bkt_148_);
v_buckets_x27_155_ = lean_array_uset(v_buckets_130_, v___x_147_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_mul(v_size_x27_153_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = lean_nat_div(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_array_get_size(v_buckets_x27_155_);
v___x_161_ = lean_nat_dec_le(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
if (v___x_161_ == 0)
{
lean_object* v_val_162_; lean_object* v___x_164_; 
v_val_162_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_155_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_val_162_);
lean_ctor_set(v___x_132_, 0, v_size_x27_153_);
v___x_164_ = v___x_132_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_val_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_167_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_buckets_x27_155_);
lean_ctor_set(v___x_132_, 0, v_size_x27_153_);
v___x_167_ = v___x_132_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_buckets_x27_155_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v___x_169_; lean_object* v_buckets_x27_170_; lean_object* v_bkt_x27_171_; uint8_t v___x_172_; 
lean_inc(v_bkt_148_);
lean_del_object(v___x_132_);
v___x_169_ = lean_box(0);
v_buckets_x27_170_ = lean_array_uset(v_buckets_130_, v___x_147_, v___x_169_);
lean_inc(v_a_121_);
v_bkt_x27_171_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_119_, v_a_121_, v_bkt_148_);
v___x_172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_121_, v_bkt_x27_171_);
lean_dec(v_a_121_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_sub(v_size_129_, v___x_173_);
lean_dec(v_size_129_);
v___y_123_ = v_buckets_x27_170_;
v___y_124_ = v___x_147_;
v___y_125_ = v_bkt_x27_171_;
v___y_126_ = v___x_174_;
goto v___jp_122_;
}
else
{
v___y_123_ = v_buckets_x27_170_;
v___y_124_ = v___x_147_;
v___y_125_ = v_bkt_x27_171_;
v___y_126_ = v_size_129_;
goto v___jp_122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_val_178_, lean_object* v_as_179_, size_t v_sz_180_, size_t v_i_181_, lean_object* v_b_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_lt(v_i_181_, v_sz_180_);
if (v___x_183_ == 0)
{
lean_dec(v_val_178_);
return v_b_182_;
}
else
{
lean_object* v_a_184_; lean_object* v_declName_185_; lean_object* v___x_186_; size_t v___x_187_; size_t v___x_188_; 
v_a_184_ = lean_array_uget_borrowed(v_as_179_, v_i_181_);
v_declName_185_ = lean_ctor_get(v_a_184_, 1);
lean_inc(v_declName_185_);
lean_inc(v_val_178_);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_178_, v_b_182_, v_declName_185_);
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_181_, v___x_187_);
v_i_181_ = v___x_188_;
v_b_182_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_val_190_, lean_object* v_as_191_, lean_object* v_sz_192_, lean_object* v_i_193_, lean_object* v_b_194_){
_start:
{
size_t v_sz_boxed_195_; size_t v_i_boxed_196_; lean_object* v_res_197_; 
v_sz_boxed_195_ = lean_unbox_usize(v_sz_192_);
lean_dec(v_sz_192_);
v_i_boxed_196_ = lean_unbox_usize(v_i_193_);
lean_dec(v_i_193_);
v_res_197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_190_, v_as_191_, v_sz_boxed_195_, v_i_boxed_196_, v_b_194_);
lean_dec_ref(v_as_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_as_198_, size_t v_sz_199_, size_t v_i_200_, lean_object* v_b_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_lt(v_i_200_, v_sz_199_);
if (v___x_202_ == 0)
{
return v_b_201_;
}
else
{
lean_object* v_snd_203_; 
v_snd_203_ = lean_ctor_get(v_b_201_, 1);
lean_inc(v_snd_203_);
if (lean_obj_tag(v_snd_203_) == 0)
{
lean_object* v_fst_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_fst_204_ = lean_ctor_get(v_b_201_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_b_201_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_b_201_, 1);
lean_dec(v_unused_212_);
v___x_206_ = v_b_201_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_fst_204_);
lean_dec(v_b_201_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_snd_203_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v_fst_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_237_; 
v_fst_213_ = lean_ctor_get(v_b_201_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_b_201_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_b_201_, 1);
lean_dec(v_unused_238_);
v___x_215_ = v_b_201_;
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_fst_213_);
lean_dec(v_b_201_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_val_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_236_; 
v_val_217_ = lean_ctor_get(v_snd_203_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_snd_203_);
if (v_isSharedCheck_236_ == 0)
{
v___x_219_ = v_snd_203_;
v_isShared_220_ = v_isSharedCheck_236_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_val_217_);
lean_dec(v_snd_203_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_236_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v_a_221_ = lean_array_uget_borrowed(v_as_198_, v_i_200_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_val_217_, v___x_222_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_223_);
v___x_225_ = v___x_219_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_235_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
size_t v_sz_226_; size_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v_sz_226_ = lean_array_size(v_a_221_);
v___x_227_ = ((size_t)0ULL);
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_217_, v_a_221_, v_sz_226_, v___x_227_, v_fst_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_225_);
lean_ctor_set(v___x_215_, 0, v___x_228_);
v___x_230_ = v___x_215_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_225_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
size_t v___x_231_; size_t v___x_232_; 
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_i_200_, v___x_231_);
v_i_200_ = v___x_232_;
v_b_201_ = v___x_230_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_239_, lean_object* v_sz_240_, lean_object* v_i_241_, lean_object* v_b_242_){
_start:
{
size_t v_sz_boxed_243_; size_t v_i_boxed_244_; lean_object* v_res_245_; 
v_sz_boxed_243_ = lean_unbox_usize(v_sz_240_);
lean_dec(v_sz_240_);
v_i_boxed_244_ = lean_unbox_usize(v_i_241_);
lean_dec(v_i_241_);
v_res_245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_239_, v_sz_boxed_243_, v_i_boxed_244_, v_b_242_);
lean_dec_ref(v_as_239_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_unsigned_to_nat(16u);
v___x_248_ = lean_mk_array(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_s_251_; 
v___x_249_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_250_ = lean_unsigned_to_nat(0u);
v_s_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_251_, 0, v___x_250_);
lean_ctor_set(v_s_251_, 1, v___x_249_);
return v_s_251_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_254_; lean_object* v_s_255_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_255_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_s_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_257_){
_start:
{
lean_object* v___x_258_; size_t v_sz_259_; size_t v___x_260_; lean_object* v___x_261_; lean_object* v_fst_262_; 
v___x_258_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_259_ = lean_array_size(v_es_257_);
v___x_260_ = ((size_t)0ULL);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_257_, v_sz_259_, v___x_260_, v___x_258_);
v_fst_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_fst_262_);
lean_dec_ref(v___x_261_);
return v_fst_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_263_);
lean_dec_ref(v_es_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_282_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_284_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_285_, lean_object* v_a_286_, lean_object* v_x_287_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_286_, v_x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_289_, lean_object* v_a_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_289_, v_a_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec(v_a_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_294_, lean_object* v_data_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_297_, lean_object* v_i_298_, lean_object* v_source_299_, lean_object* v_target_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_298_, v_source_299_, v_target_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_303_, v_x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__2(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_309_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_310_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object* v_env_314_, lean_object* v_modIdx_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__3, &l_Lean_getIndirectModUses___closed__3_once, _init_l_Lean_getIndirectModUses___closed__3);
v___x_317_ = l_Lean_indirectModUseExt;
v___x_318_ = 0;
v___x_319_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_316_, v___x_317_, v_env_314_, v_modIdx_315_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object* v_env_320_, lean_object* v_modIdx_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_getIndirectModUses(v_env_320_, v_modIdx_321_);
lean_dec(v_modIdx_321_);
lean_dec_ref(v_env_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object* v___x_323_, lean_object* v___x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_toEnvExtension_326_; lean_object* v_asyncMode_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_toEnvExtension_326_ = lean_ctor_get(v___x_323_, 0);
v_asyncMode_327_ = lean_ctor_get(v_toEnvExtension_326_, 2);
lean_inc(v_asyncMode_327_);
v___x_328_ = lean_box(0);
v___x_329_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_323_, v_x_325_, v___x_324_, v_asyncMode_327_, v___x_328_);
lean_dec(v_asyncMode_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object* v_modifyEnv_330_, lean_object* v___f_331_, lean_object* v_____r_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_apply_1(v_modifyEnv_330_, v___f_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__0));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__2));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__4));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object* v_modifyEnv_343_, lean_object* v___f_344_, lean_object* v_declName_345_, lean_object* v_kind_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_cls_351_, lean_object* v_toBind_352_, lean_object* v___f_353_, uint8_t v_____do__lift_354_){
_start:
{
if (v_____do__lift_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec(v___f_353_);
lean_dec(v_toBind_352_);
lean_dec(v_cls_351_);
lean_dec(v_inst_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_kind_346_);
lean_dec(v_declName_345_);
v___x_355_ = lean_apply_1(v_modifyEnv_343_, v___f_344_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v___f_344_);
lean_dec(v_modifyEnv_343_);
v___x_356_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__1, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1);
v___x_357_ = l_Lean_MessageData_ofName(v_declName_345_);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__3, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__3_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_stringToMessageData(v_kind_346_);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__2___closed__5, &l_Lean_recordIndirectModUse___redArg___lam__2___closed__5_once, _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_Lean_addTrace___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_cls_351_, v___x_364_);
v___x_366_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v___x_365_, v___f_353_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object* v_modifyEnv_367_, lean_object* v___f_368_, lean_object* v_declName_369_, lean_object* v_kind_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_cls_375_, lean_object* v_toBind_376_, lean_object* v___f_377_, lean_object* v_____do__lift_378_){
_start:
{
uint8_t v_____do__lift_579__boxed_379_; lean_object* v_res_380_; 
v_____do__lift_579__boxed_379_ = lean_unbox(v_____do__lift_378_);
v_res_380_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_modifyEnv_367_, v___f_368_, v_declName_369_, v_kind_370_, v_inst_371_, v_inst_372_, v_inst_373_, v_inst_374_, v_cls_375_, v_toBind_376_, v___f_377_, v_____do__lift_579__boxed_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v_toPure_384_, lean_object* v_cls_385_, lean_object* v_____do__lift_386_, lean_object* v_____do__lift_387_){
_start:
{
uint8_t v_hasTrace_388_; 
v_hasTrace_388_ = lean_ctor_get_uint8(v_____do__lift_387_, sizeof(void*)*1);
if (v_hasTrace_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_cls_385_);
v___x_389_ = lean_box(v_hasTrace_388_);
v___x_390_ = lean_apply_2(v_toPure_384_, lean_box(0), v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_391_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1));
v___x_392_ = l_Lean_Name_append(v___x_391_, v_cls_385_);
v___x_393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_386_, v_____do__lift_387_, v___x_392_);
lean_dec(v___x_392_);
v___x_394_ = lean_box(v___x_393_);
v___x_395_ = lean_apply_2(v_toPure_384_, lean_box(0), v___x_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3___boxed(lean_object* v_toPure_396_, lean_object* v_cls_397_, lean_object* v_____do__lift_398_, lean_object* v_____do__lift_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_recordIndirectModUse___redArg___lam__3(v_toPure_396_, v_cls_397_, v_____do__lift_398_, v_____do__lift_399_);
lean_dec_ref(v_____do__lift_399_);
lean_dec_ref(v_____do__lift_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object* v_toPure_401_, lean_object* v_cls_402_, lean_object* v_toBind_403_, lean_object* v_inst_404_, lean_object* v_____do__lift_405_){
_start:
{
lean_object* v___f_406_; lean_object* v___x_407_; 
v___f_406_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_406_, 0, v_toPure_401_);
lean_closure_set(v___f_406_, 1, v_cls_402_);
lean_closure_set(v___f_406_, 2, v_____do__lift_405_);
v___x_407_ = lean_apply_4(v_toBind_403_, lean_box(0), lean_box(0), v_inst_404_, v___f_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v___x_411_, lean_object* v_kind_412_, lean_object* v_declName_413_, lean_object* v___x_414_, lean_object* v_inst_415_, lean_object* v_toApplicative_416_, lean_object* v_modifyEnv_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_toBind_421_, lean_object* v_inst_422_, lean_object* v_____do__lift_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_424_ = l_Lean_indirectModUseExt;
v___x_425_ = lean_box(2);
v___x_426_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_411_, v___x_424_, v_____do__lift_423_, v___x_425_);
lean_inc(v_declName_413_);
lean_inc_ref(v_kind_412_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_kind_412_);
lean_ctor_set(v___x_427_, 1, v_declName_413_);
lean_inc_ref(v___x_427_);
v___x_428_ = l_List_elem___redArg(v___x_414_, v___x_427_, v___x_426_);
if (v___x_428_ == 0)
{
lean_object* v_getInheritedTraceOptions_429_; lean_object* v_toPure_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v_cls_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_getInheritedTraceOptions_429_ = lean_ctor_get(v_inst_415_, 2);
lean_inc(v_getInheritedTraceOptions_429_);
v_toPure_430_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_430_);
lean_dec_ref(v_toApplicative_416_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_431_, 0, v___x_424_);
lean_closure_set(v___f_431_, 1, v___x_427_);
lean_inc_ref(v___f_431_);
lean_inc(v_modifyEnv_417_);
v___f_432_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_432_, 0, v_modifyEnv_417_);
lean_closure_set(v___f_432_, 1, v___f_431_);
v_cls_433_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_421_, 3);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_434_, 0, v_modifyEnv_417_);
lean_closure_set(v___f_434_, 1, v___f_431_);
lean_closure_set(v___f_434_, 2, v_declName_413_);
lean_closure_set(v___f_434_, 3, v_kind_412_);
lean_closure_set(v___f_434_, 4, v_inst_418_);
lean_closure_set(v___f_434_, 5, v_inst_415_);
lean_closure_set(v___f_434_, 6, v_inst_419_);
lean_closure_set(v___f_434_, 7, v_inst_420_);
lean_closure_set(v___f_434_, 8, v_cls_433_);
lean_closure_set(v___f_434_, 9, v_toBind_421_);
lean_closure_set(v___f_434_, 10, v___f_432_);
v___f_435_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_435_, 0, v_toPure_430_);
lean_closure_set(v___f_435_, 1, v_cls_433_);
lean_closure_set(v___f_435_, 2, v_toBind_421_);
lean_closure_set(v___f_435_, 3, v_inst_422_);
v___x_436_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_429_, v___f_435_);
v___x_437_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_436_, v___f_434_);
return v___x_437_;
}
else
{
lean_object* v_toPure_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref_known(v___x_427_, 2);
lean_dec(v_inst_422_);
lean_dec(v_toBind_421_);
lean_dec(v_inst_420_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
lean_dec(v_modifyEnv_417_);
lean_dec_ref(v_inst_415_);
lean_dec(v_declName_413_);
lean_dec_ref(v_kind_412_);
v_toPure_438_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_438_);
lean_dec_ref(v_toApplicative_416_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_apply_2(v_toPure_438_, lean_box(0), v___x_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_kind_447_, lean_object* v_declName_448_){
_start:
{
lean_object* v_toApplicative_449_; lean_object* v_toBind_450_; lean_object* v_getEnv_451_; lean_object* v_modifyEnv_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v_toApplicative_449_ = lean_ctor_get(v_inst_441_, 0);
lean_inc_ref(v_toApplicative_449_);
v_toBind_450_ = lean_ctor_get(v_inst_441_, 1);
lean_inc_n(v_toBind_450_, 2);
v_getEnv_451_ = lean_ctor_get(v_inst_442_, 0);
lean_inc(v_getEnv_451_);
v_modifyEnv_452_ = lean_ctor_get(v_inst_442_, 1);
lean_inc(v_modifyEnv_452_);
lean_dec_ref(v_inst_442_);
v___x_453_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_454_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5), 13, 12);
lean_closure_set(v___f_455_, 0, v___x_454_);
lean_closure_set(v___f_455_, 1, v_kind_447_);
lean_closure_set(v___f_455_, 2, v_declName_448_);
lean_closure_set(v___f_455_, 3, v___x_453_);
lean_closure_set(v___f_455_, 4, v_inst_443_);
lean_closure_set(v___f_455_, 5, v_toApplicative_449_);
lean_closure_set(v___f_455_, 6, v_modifyEnv_452_);
lean_closure_set(v___f_455_, 7, v_inst_441_);
lean_closure_set(v___f_455_, 8, v_inst_445_);
lean_closure_set(v___f_455_, 9, v_inst_446_);
lean_closure_set(v___f_455_, 10, v_toBind_450_);
lean_closure_set(v___f_455_, 11, v_inst_444_);
v___x_456_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v_getEnv_451_, v___f_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_kind_464_, lean_object* v_declName_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_recordIndirectModUse___redArg(v_inst_458_, v_inst_459_, v_inst_460_, v_inst_461_, v_inst_462_, v_inst_463_, v_kind_464_, v_declName_465_);
return v___x_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_module_469_; uint8_t v_isExported_470_; uint8_t v_isMeta_471_; lean_object* v_module_472_; uint8_t v_isExported_473_; uint8_t v_isMeta_474_; uint8_t v___y_476_; uint8_t v___x_477_; 
v_module_469_ = lean_ctor_get(v_x_467_, 0);
v_isExported_470_ = lean_ctor_get_uint8(v_x_467_, sizeof(void*)*1);
v_isMeta_471_ = lean_ctor_get_uint8(v_x_467_, sizeof(void*)*1 + 1);
v_module_472_ = lean_ctor_get(v_x_468_, 0);
v_isExported_473_ = lean_ctor_get_uint8(v_x_468_, sizeof(void*)*1);
v_isMeta_474_ = lean_ctor_get_uint8(v_x_468_, sizeof(void*)*1 + 1);
v___x_477_ = lean_name_eq(v_module_469_, v_module_472_);
if (v___x_477_ == 0)
{
return v___x_477_;
}
else
{
if (v_isExported_470_ == 0)
{
if (v_isExported_473_ == 0)
{
v___y_476_ = v___x_477_;
goto v___jp_475_;
}
else
{
return v_isExported_470_;
}
}
else
{
v___y_476_ = v_isExported_473_;
goto v___jp_475_;
}
}
v___jp_475_:
{
if (v___y_476_ == 0)
{
return v___y_476_;
}
else
{
if (v_isMeta_471_ == 0)
{
if (v_isMeta_474_ == 0)
{
return v___y_476_;
}
else
{
return v_isMeta_471_;
}
}
else
{
return v_isMeta_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lean_instBEqExtraModUse_beq(v_x_478_, v_x_479_);
lean_dec_ref(v_x_479_);
lean_dec_ref(v_x_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_484_){
_start:
{
lean_object* v_module_485_; uint8_t v_isExported_486_; uint8_t v_isMeta_487_; uint64_t v___y_489_; uint64_t v___y_490_; uint64_t v___x_496_; uint64_t v___y_498_; 
v_module_485_ = lean_ctor_get(v_x_484_, 0);
v_isExported_486_ = lean_ctor_get_uint8(v_x_484_, sizeof(void*)*1);
v_isMeta_487_ = lean_ctor_get_uint8(v_x_484_, sizeof(void*)*1 + 1);
v___x_496_ = 0ULL;
if (lean_obj_tag(v_module_485_) == 0)
{
uint64_t v___x_502_; 
v___x_502_ = 1723ULL;
v___y_498_ = v___x_502_;
goto v___jp_497_;
}
else
{
uint64_t v_hash_503_; 
v_hash_503_ = lean_ctor_get_uint64(v_module_485_, sizeof(void*)*2);
v___y_498_ = v_hash_503_;
goto v___jp_497_;
}
v___jp_488_:
{
uint64_t v___x_491_; 
v___x_491_ = lean_uint64_mix_hash(v___y_489_, v___y_490_);
if (v_isMeta_487_ == 0)
{
uint64_t v___x_492_; uint64_t v___x_493_; 
v___x_492_ = 13ULL;
v___x_493_ = lean_uint64_mix_hash(v___x_491_, v___x_492_);
return v___x_493_;
}
else
{
uint64_t v___x_494_; uint64_t v___x_495_; 
v___x_494_ = 11ULL;
v___x_495_ = lean_uint64_mix_hash(v___x_491_, v___x_494_);
return v___x_495_;
}
}
v___jp_497_:
{
uint64_t v___x_499_; 
v___x_499_ = lean_uint64_mix_hash(v___x_496_, v___y_498_);
if (v_isExported_486_ == 0)
{
uint64_t v___x_500_; 
v___x_500_ = 13ULL;
v___y_489_ = v___x_499_;
v___y_490_ = v___x_500_;
goto v___jp_488_;
}
else
{
uint64_t v___x_501_; 
v___x_501_ = 11ULL;
v___y_489_ = v___x_499_;
v___y_490_ = v___x_501_;
goto v___jp_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_504_){
_start:
{
uint64_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Lean_instHashableExtraModUse_hash(v_x_504_);
lean_dec_ref(v_x_504_);
v_r_506_ = lean_box_uint64(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_nat_to_int(v_a_509_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(10u);
v___x_525_ = lean_nat_to_int(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(14u);
v___x_533_ = lean_nat_to_int(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_539_ = lean_string_length(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_541_ = lean_nat_to_int(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_546_){
_start:
{
lean_object* v_module_547_; uint8_t v_isExported_548_; uint8_t v_isMeta_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_module_547_ = lean_ctor_get(v_x_546_, 0);
lean_inc(v_module_547_);
v_isExported_548_ = lean_ctor_get_uint8(v_x_546_, sizeof(void*)*1);
v_isMeta_549_ = lean_ctor_get_uint8(v_x_546_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_546_);
v___x_550_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_551_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_552_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = l_Lean_Name_reprPrec(v_module_547_, v___x_553_);
v___x_555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_552_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = 0;
v___x_557_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*1, v___x_556_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_551_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_box(1);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_550_);
v___x_566_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_567_ = l_Bool_repr___redArg(v_isExported_548_);
v___x_568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*1, v___x_556_);
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_565_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_559_);
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_561_);
v___x_573_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_550_);
v___x_576_ = l_Bool_repr___redArg(v_isMeta_549_);
v___x_577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_552_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set_uint8(v___x_578_, sizeof(void*)*1, v___x_556_);
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_575_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_581_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_579_);
v___x_583_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_580_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_586_, sizeof(void*)*1, v___x_556_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_587_, lean_object* v_prec_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_590_, lean_object* v_prec_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_instReprExtraModUse_repr(v_x_590_, v_prec_591_);
lean_dec(v_prec_591_);
return v_res_592_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_595_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_entries_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_606_ = lean_array_mk(v_entries_604_);
v___x_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_entries_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_608_, v_x_609_, v_entries_610_);
lean_dec_ref(v_x_609_);
lean_dec_ref(v_x_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_array_mk(v_es_612_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_box(0));
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_617_);
lean_dec_ref(v_x_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_ks_623_; lean_object* v_vs_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_648_; 
v_ks_623_ = lean_ctor_get(v_x_619_, 0);
v_vs_624_ = lean_ctor_get(v_x_619_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_619_);
if (v_isSharedCheck_648_ == 0)
{
v___x_626_ = v_x_619_;
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_vs_624_);
lean_inc(v_ks_623_);
lean_dec(v_x_619_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_array_get_size(v_ks_623_);
v___x_629_ = lean_nat_dec_lt(v_x_620_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
lean_dec(v_x_620_);
v___x_630_ = lean_array_push(v_ks_623_, v_x_621_);
v___x_631_ = lean_array_push(v_vs_624_, v_x_622_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_631_);
lean_ctor_set(v___x_626_, 0, v___x_630_);
v___x_633_ = v___x_626_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v_k_x27_635_; uint8_t v___x_636_; 
v_k_x27_635_ = lean_array_fget_borrowed(v_ks_623_, v_x_620_);
v___x_636_ = l_Lean_instBEqExtraModUse_beq(v_x_621_, v_k_x27_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_638_; 
if (v_isShared_627_ == 0)
{
v___x_638_ = v___x_626_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_ks_623_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_vs_624_);
v___x_638_ = v_reuseFailAlloc_642_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v_x_620_, v___x_639_);
lean_dec(v_x_620_);
v_x_619_ = v___x_638_;
v_x_620_ = v___x_640_;
goto _start;
}
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_643_ = lean_array_fset(v_ks_623_, v_x_620_, v_x_621_);
v___x_644_ = lean_array_fset(v_vs_624_, v_x_620_, v_x_622_);
lean_dec(v_x_620_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_644_);
lean_ctor_set(v___x_626_, 0, v___x_643_);
v___x_646_ = v___x_626_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_649_, lean_object* v_k_650_, lean_object* v_v_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_649_, v___x_652_, v_k_650_, v_v_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_655_, size_t v_x_656_, size_t v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v_es_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v_j_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_es_660_ = lean_ctor_get(v_x_655_, 0);
v___x_661_ = ((size_t)31ULL);
v___x_662_ = lean_usize_land(v_x_656_, v___x_661_);
v_j_663_ = lean_usize_to_nat(v___x_662_);
v___x_664_ = lean_array_get_size(v_es_660_);
v___x_665_ = lean_nat_dec_lt(v_j_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_j_663_);
lean_dec(v_x_659_);
lean_dec_ref(v_x_658_);
return v_x_655_;
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_704_; 
lean_inc_ref(v_es_660_);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_x_655_, 0);
lean_dec(v_unused_705_);
v___x_667_ = v_x_655_;
v_isShared_668_ = v_isSharedCheck_704_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_x_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_704_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_v_669_; lean_object* v___x_670_; lean_object* v_xs_x27_671_; lean_object* v___y_673_; 
v_v_669_ = lean_array_fget(v_es_660_, v_j_663_);
v___x_670_ = lean_box(0);
v_xs_x27_671_ = lean_array_fset(v_es_660_, v_j_663_, v___x_670_);
switch(lean_obj_tag(v_v_669_))
{
case 0:
{
lean_object* v_key_678_; lean_object* v_val_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v_key_678_ = lean_ctor_get(v_v_669_, 0);
v_val_679_ = lean_ctor_get(v_v_669_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_v_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v_v_669_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_val_679_);
lean_inc(v_key_678_);
lean_dec(v_v_669_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_instBEqExtraModUse_beq(v_x_658_, v_key_678_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_del_object(v___x_681_);
v___x_684_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_678_, v_val_679_, v_x_658_, v_x_659_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
v___y_673_ = v___x_685_;
goto v___jp_672_;
}
else
{
lean_object* v___x_687_; 
lean_dec(v_val_679_);
lean_dec(v_key_678_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_x_659_);
lean_ctor_set(v___x_681_, 0, v_x_658_);
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_x_658_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_x_659_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v___y_673_ = v___x_687_;
goto v___jp_672_;
}
}
}
}
case 1:
{
lean_object* v_node_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
v_node_690_ = lean_ctor_get(v_v_669_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_v_669_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v_v_669_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_node_690_);
lean_dec(v_v_669_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_694_ = ((size_t)5ULL);
v___x_695_ = lean_usize_shift_right(v_x_656_, v___x_694_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_x_657_, v___x_696_);
v___x_698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_690_, v___x_695_, v___x_697_, v_x_658_, v_x_659_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_698_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v___y_673_ = v___x_700_;
goto v___jp_672_;
}
}
}
default: 
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_x_658_);
lean_ctor_set(v___x_703_, 1, v_x_659_);
v___y_673_ = v___x_703_;
goto v___jp_672_;
}
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_array_fset(v_xs_x27_671_, v_j_663_, v___y_673_);
lean_dec(v_j_663_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_674_);
v___x_676_ = v___x_667_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_object* v_ks_706_; lean_object* v_vs_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_727_; 
v_ks_706_ = lean_ctor_get(v_x_655_, 0);
v_vs_707_ = lean_ctor_get(v_x_655_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_727_ == 0)
{
v___x_709_ = v_x_655_;
v_isShared_710_ = v_isSharedCheck_727_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_vs_707_);
lean_inc(v_ks_706_);
lean_dec(v_x_655_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_727_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_ks_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_vs_707_);
v___x_712_ = v_reuseFailAlloc_726_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v_newNode_713_; uint8_t v___y_715_; size_t v___x_721_; uint8_t v___x_722_; 
v_newNode_713_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_712_, v_x_658_, v_x_659_);
v___x_721_ = ((size_t)7ULL);
v___x_722_ = lean_usize_dec_le(v___x_721_, v_x_657_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_713_);
v___x_724_ = lean_unsigned_to_nat(4u);
v___x_725_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
lean_dec(v___x_723_);
v___y_715_ = v___x_725_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___x_722_;
goto v___jp_714_;
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
lean_object* v_ks_716_; lean_object* v_vs_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_ks_716_ = lean_ctor_get(v_newNode_713_, 0);
lean_inc_ref(v_ks_716_);
v_vs_717_ = lean_ctor_get(v_newNode_713_, 1);
lean_inc_ref(v_vs_717_);
lean_dec_ref(v_newNode_713_);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_657_, v_ks_716_, v_vs_717_, v___x_718_, v___x_719_);
lean_dec_ref(v_vs_717_);
lean_dec_ref(v_ks_716_);
return v___x_720_;
}
else
{
return v_newNode_713_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_728_, lean_object* v_keys_729_, lean_object* v_vals_730_, lean_object* v_i_731_, lean_object* v_entries_732_){
_start:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_array_get_size(v_keys_729_);
v___x_734_ = lean_nat_dec_lt(v_i_731_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec(v_i_731_);
return v_entries_732_;
}
else
{
lean_object* v_k_735_; lean_object* v_v_736_; uint64_t v___x_737_; size_t v_h_738_; size_t v___x_739_; lean_object* v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v_h_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_k_735_ = lean_array_fget_borrowed(v_keys_729_, v_i_731_);
v_v_736_ = lean_array_fget_borrowed(v_vals_730_, v_i_731_);
v___x_737_ = l_Lean_instHashableExtraModUse_hash(v_k_735_);
v_h_738_ = lean_uint64_to_usize(v___x_737_);
v___x_739_ = ((size_t)5ULL);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_sub(v_depth_728_, v___x_741_);
v___x_743_ = lean_usize_mul(v___x_739_, v___x_742_);
v_h_744_ = lean_usize_shift_right(v_h_738_, v___x_743_);
v___x_745_ = lean_nat_add(v_i_731_, v___x_740_);
lean_dec(v_i_731_);
lean_inc(v_v_736_);
lean_inc(v_k_735_);
v___x_746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_732_, v_h_744_, v_depth_728_, v_k_735_, v_v_736_);
v_i_731_ = v___x_745_;
v_entries_732_ = v___x_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_748_, lean_object* v_keys_749_, lean_object* v_vals_750_, lean_object* v_i_751_, lean_object* v_entries_752_){
_start:
{
size_t v_depth_boxed_753_; lean_object* v_res_754_; 
v_depth_boxed_753_ = lean_unbox_usize(v_depth_748_);
lean_dec(v_depth_748_);
v_res_754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_753_, v_keys_749_, v_vals_750_, v_i_751_, v_entries_752_);
lean_dec_ref(v_vals_750_);
lean_dec_ref(v_keys_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
size_t v_x_567__boxed_760_; size_t v_x_568__boxed_761_; lean_object* v_res_762_; 
v_x_567__boxed_760_ = lean_unbox_usize(v_x_756_);
lean_dec(v_x_756_);
v_x_568__boxed_761_ = lean_unbox_usize(v_x_757_);
lean_dec(v_x_757_);
v_res_762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_755_, v_x_567__boxed_760_, v_x_568__boxed_761_, v_x_758_, v_x_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
uint64_t v___x_766_; size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_766_ = l_Lean_instHashableExtraModUse_hash(v_x_764_);
v___x_767_ = lean_uint64_to_usize(v___x_766_);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_763_, v___x_767_, v___x_768_, v_x_764_, v_x_765_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_770_, lean_object* v_k_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_box(0);
v___x_773_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_770_, v_k_771_, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_774_, lean_object* v_i_775_, lean_object* v_k_776_){
_start:
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = lean_array_get_size(v_keys_774_);
v___x_778_ = lean_nat_dec_lt(v_i_775_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec(v_i_775_);
return v___x_778_;
}
else
{
lean_object* v_k_x27_779_; uint8_t v___x_780_; 
v_k_x27_779_ = lean_array_fget_borrowed(v_keys_774_, v_i_775_);
v___x_780_ = l_Lean_instBEqExtraModUse_beq(v_k_776_, v_k_x27_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_i_775_, v___x_781_);
lean_dec(v_i_775_);
v_i_775_ = v___x_782_;
goto _start;
}
else
{
lean_dec(v_i_775_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_784_, lean_object* v_i_785_, lean_object* v_k_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_784_, v_i_785_, v_k_786_);
lean_dec_ref(v_k_786_);
lean_dec_ref(v_keys_784_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_789_, size_t v_x_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_object* v_es_792_; lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; lean_object* v_j_796_; lean_object* v___x_797_; 
v_es_792_ = lean_ctor_get(v_x_789_, 0);
v___x_793_ = lean_box(2);
v___x_794_ = ((size_t)31ULL);
v___x_795_ = lean_usize_land(v_x_790_, v___x_794_);
v_j_796_ = lean_usize_to_nat(v___x_795_);
v___x_797_ = lean_array_get_borrowed(v___x_793_, v_es_792_, v_j_796_);
lean_dec(v_j_796_);
switch(lean_obj_tag(v___x_797_))
{
case 0:
{
lean_object* v_key_798_; uint8_t v___x_799_; 
v_key_798_ = lean_ctor_get(v___x_797_, 0);
v___x_799_ = l_Lean_instBEqExtraModUse_beq(v_x_791_, v_key_798_);
return v___x_799_;
}
case 1:
{
lean_object* v_node_800_; size_t v___x_801_; size_t v___x_802_; 
v_node_800_ = lean_ctor_get(v___x_797_, 0);
v___x_801_ = ((size_t)5ULL);
v___x_802_ = lean_usize_shift_right(v_x_790_, v___x_801_);
v_x_789_ = v_node_800_;
v_x_790_ = v___x_802_;
goto _start;
}
default: 
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
}
}
else
{
lean_object* v_ks_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_ks_805_ = lean_ctor_get(v_x_789_, 0);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_805_, v___x_806_, v_x_791_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
size_t v_x_753__boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_x_753__boxed_811_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_res_812_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_808_, v_x_753__boxed_811_, v_x_810_);
lean_dec_ref(v_x_810_);
lean_dec_ref(v_x_808_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
uint64_t v___x_816_; size_t v___x_817_; uint8_t v___x_818_; 
v___x_816_ = l_Lean_instHashableExtraModUse_hash(v_x_815_);
v___x_817_ = lean_uint64_to_usize(v___x_816_);
v___x_818_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_814_, v___x_817_, v_x_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_819_, v_x_820_);
lean_dec_ref(v_x_820_);
lean_dec_ref(v_x_819_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_865_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_867_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
uint8_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_872_, v_x_873_, v_x_874_);
lean_dec_ref(v_x_874_);
lean_dec_ref(v_x_873_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_878_, v_x_879_, v_x_880_);
return v___x_881_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, size_t v_x_884_, lean_object* v_x_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_883_, v_x_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
size_t v_x_951__boxed_891_; uint8_t v_res_892_; lean_object* v_r_893_; 
v_x_951__boxed_891_ = lean_unbox_usize(v_x_889_);
lean_dec(v_x_889_);
v_res_892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_887_, v_x_888_, v_x_951__boxed_891_, v_x_890_);
lean_dec_ref(v_x_890_);
lean_dec_ref(v_x_888_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, size_t v_x_896_, size_t v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_895_, v_x_896_, v_x_897_, v_x_898_, v_x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
size_t v_x_962__boxed_907_; size_t v_x_963__boxed_908_; lean_object* v_res_909_; 
v_x_962__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_x_963__boxed_908_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_901_, v_x_902_, v_x_962__boxed_907_, v_x_963__boxed_908_, v_x_905_, v_x_906_);
return v_res_909_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_heq_913_, lean_object* v_i_914_, lean_object* v_k_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_911_, v_i_914_, v_k_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_917_, lean_object* v_keys_918_, lean_object* v_vals_919_, lean_object* v_heq_920_, lean_object* v_i_921_, lean_object* v_k_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_917_, v_keys_918_, v_vals_919_, v_heq_920_, v_i_921_, v_k_922_);
lean_dec_ref(v_k_922_);
lean_dec_ref(v_vals_919_);
lean_dec_ref(v_keys_918_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_925_, lean_object* v_n_926_, lean_object* v_k_927_, lean_object* v_v_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_926_, v_k_927_, v_v_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_930_, size_t v_depth_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_heq_934_, lean_object* v_i_935_, lean_object* v_entries_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_931_, v_keys_932_, v_vals_933_, v_i_935_, v_entries_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_938_, lean_object* v_depth_939_, lean_object* v_keys_940_, lean_object* v_vals_941_, lean_object* v_heq_942_, lean_object* v_i_943_, lean_object* v_entries_944_){
_start:
{
size_t v_depth_boxed_945_; lean_object* v_res_946_; 
v_depth_boxed_945_ = lean_unbox_usize(v_depth_939_);
lean_dec(v_depth_939_);
v_res_946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_938_, v_depth_boxed_945_, v_keys_940_, v_vals_941_, v_heq_942_, v_i_943_, v_entries_944_);
lean_dec_ref(v_vals_941_);
lean_dec_ref(v_keys_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_948_, v_x_949_, v_x_950_, v_x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_954_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_955_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_954_, v___x_953_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_957_ = lean_box(0);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_959_, lean_object* v_modIdx_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
v___x_961_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_962_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_963_ = 0;
v___x_964_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_961_, v___x_962_, v_env_959_, v_modIdx_960_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_965_, lean_object* v_modIdx_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_getExtraModUses(v_env_965_, v_modIdx_966_);
lean_dec(v_modIdx_966_);
lean_dec_ref(v_env_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_968_, lean_object* v_b_969_){
_start:
{
if (lean_obj_tag(v_as_x27_968_) == 0)
{
return v_b_969_;
}
else
{
lean_object* v_head_970_; lean_object* v_tail_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_head_970_ = lean_ctor_get(v_as_x27_968_, 0);
v_tail_971_ = lean_ctor_get(v_as_x27_968_, 1);
v___x_972_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_973_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_974_ = lean_box(1);
v___x_975_ = lean_box(0);
lean_inc_ref(v_b_969_);
v___x_976_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_972_, v___x_973_, v_b_969_, v___x_974_, v___x_975_);
v___x_977_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_976_, v_head_970_);
lean_dec(v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v_toEnvExtension_978_; lean_object* v_asyncMode_979_; lean_object* v___x_980_; 
v_toEnvExtension_978_ = lean_ctor_get(v___x_973_, 0);
v_asyncMode_979_ = lean_ctor_get(v_toEnvExtension_978_, 2);
lean_inc(v_head_970_);
v___x_980_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_973_, v_b_969_, v_head_970_, v_asyncMode_979_, v___x_975_);
v_as_x27_968_ = v_tail_971_;
v_b_969_ = v___x_980_;
goto _start;
}
else
{
v_as_x27_968_ = v_tail_971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_983_, lean_object* v_b_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_983_, v_b_984_);
lean_dec(v_as_x27_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_986_, lean_object* v_dest_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_988_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_989_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_990_ = lean_box(1);
v___x_991_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_988_, v___x_989_, v_src_986_, v___x_990_);
v___x_992_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_991_, v_dest_987_);
lean_dec(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_993_, lean_object* v_as_x27_994_, lean_object* v_b_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_994_, v_b_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_998_, lean_object* v_as_x27_999_, lean_object* v_b_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_998_, v_as_x27_999_, v_b_1000_, v_a_1001_);
lean_dec(v_as_x27_999_);
lean_dec(v_as_998_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1003_, lean_object* v_entry_1004_, lean_object* v___x_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v_toEnvExtension_1007_; lean_object* v_asyncMode_1008_; lean_object* v___x_1009_; 
v_toEnvExtension_1007_ = lean_ctor_get(v___x_1003_, 0);
v_asyncMode_1008_ = lean_ctor_get(v_toEnvExtension_1007_, 2);
lean_inc(v_asyncMode_1008_);
v___x_1009_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1003_, v_x_1006_, v_entry_1004_, v_asyncMode_1008_, v___x_1005_);
lean_dec(v_asyncMode_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_modifyEnv_1029_, lean_object* v___f_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_cls_1035_, lean_object* v_toBind_1036_, lean_object* v___f_1037_, lean_object* v_mod_1038_, lean_object* v_hint_1039_, uint8_t v_isMeta_1040_, uint8_t v_isExporting_1041_, uint8_t v_____do__lift_1042_){
_start:
{
lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1050_; lean_object* v___y_1051_; 
if (v_____do__lift_1042_ == 0)
{
lean_object* v___x_1063_; 
lean_dec(v_hint_1039_);
lean_dec(v_mod_1038_);
lean_dec(v___f_1037_);
lean_dec(v_toBind_1036_);
lean_dec(v_cls_1035_);
lean_dec(v_inst_1034_);
lean_dec_ref(v_inst_1033_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_inst_1031_);
v___x_1063_ = lean_apply_1(v_modifyEnv_1029_, v___f_1030_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___y_1066_; 
lean_dec_ref(v___f_1030_);
lean_dec(v_modifyEnv_1029_);
v___x_1064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
if (v_isExporting_1041_ == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12));
v___y_1066_ = v___x_1073_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13));
v___y_1066_ = v___x_1074_;
goto v___jp_1065_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_inc_ref(v___y_1066_);
v___x_1067_ = l_Lean_stringToMessageData(v___y_1066_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1064_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
if (v_isMeta_1040_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10));
v___y_1050_ = v___x_1070_;
v___y_1051_ = v___x_1071_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11));
v___y_1050_ = v___x_1070_;
v___y_1051_ = v___x_1072_;
goto v___jp_1049_;
}
}
}
v___jp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___y_1044_);
lean_ctor_set(v___x_1046_, 1, v___y_1045_);
v___x_1047_ = l_Lean_addTrace___redArg(v_inst_1031_, v_inst_1032_, v_inst_1033_, v_inst_1034_, v_cls_1035_, v___x_1046_);
v___x_1048_ = lean_apply_4(v_toBind_1036_, lean_box(0), lean_box(0), v___x_1047_, v___f_1037_);
return v___x_1048_;
}
v___jp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
lean_inc_ref(v___y_1051_);
v___x_1052_ = l_Lean_stringToMessageData(v___y_1051_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1050_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_ofName(v_mod_1038_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_Name_isAnonymous(v_hint_1039_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
v___x_1060_ = l_Lean_MessageData_ofName(v_hint_1039_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___y_1044_ = v___x_1057_;
v___y_1045_ = v___x_1061_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1062_; 
lean_dec(v_hint_1039_);
v___x_1062_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
v___y_1044_ = v___x_1057_;
v___y_1045_ = v___x_1062_;
goto v___jp_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_modifyEnv_1075_, lean_object* v___f_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_cls_1081_, lean_object* v_toBind_1082_, lean_object* v___f_1083_, lean_object* v_mod_1084_, lean_object* v_hint_1085_, lean_object* v_isMeta_1086_, lean_object* v_isExporting_1087_, lean_object* v_____do__lift_1088_){
_start:
{
uint8_t v_isMeta_boxed_1089_; uint8_t v_isExporting_boxed_1090_; uint8_t v_____do__lift_963__boxed_1091_; lean_object* v_res_1092_; 
v_isMeta_boxed_1089_ = lean_unbox(v_isMeta_1086_);
v_isExporting_boxed_1090_ = lean_unbox(v_isExporting_1087_);
v_____do__lift_963__boxed_1091_ = lean_unbox(v_____do__lift_1088_);
v_res_1092_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_modifyEnv_1075_, v___f_1076_, v_inst_1077_, v_inst_1078_, v_inst_1079_, v_inst_1080_, v_cls_1081_, v_toBind_1082_, v___f_1083_, v_mod_1084_, v_hint_1085_, v_isMeta_boxed_1089_, v_isExporting_boxed_1090_, v_____do__lift_963__boxed_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v___x_1095_, lean_object* v_entry_1096_, lean_object* v_inst_1097_, lean_object* v_toApplicative_1098_, lean_object* v_modifyEnv_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_toBind_1103_, lean_object* v_mod_1104_, lean_object* v_hint_1105_, uint8_t v_isMeta_1106_, uint8_t v_isExporting_1107_, lean_object* v_inst_1108_, lean_object* v_____do__lift_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1110_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1111_ = lean_box(1);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1093_, v___x_1110_, v_____do__lift_1109_, v___x_1111_, v___x_1112_);
lean_inc_ref(v_entry_1096_);
v___x_1114_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1094_, v___x_1095_, v___x_1113_, v_entry_1096_);
if (v___x_1114_ == 0)
{
lean_object* v_getInheritedTraceOptions_1115_; lean_object* v_toPure_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v_cls_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_getInheritedTraceOptions_1115_ = lean_ctor_get(v_inst_1097_, 2);
lean_inc(v_getInheritedTraceOptions_1115_);
v_toPure_1116_ = lean_ctor_get(v_toApplicative_1098_, 1);
lean_inc(v_toPure_1116_);
lean_dec_ref(v_toApplicative_1098_);
v___f_1117_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1117_, 0, v___x_1110_);
lean_closure_set(v___f_1117_, 1, v_entry_1096_);
lean_closure_set(v___f_1117_, 2, v___x_1112_);
lean_inc_ref(v___f_1117_);
lean_inc(v_modifyEnv_1099_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1118_, 0, v_modifyEnv_1099_);
lean_closure_set(v___f_1118_, 1, v___f_1117_);
v_cls_1119_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1120_ = lean_box(v_isMeta_1106_);
v___x_1121_ = lean_box(v_isExporting_1107_);
lean_inc_n(v_toBind_1103_, 3);
v___f_1122_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1122_, 0, v_modifyEnv_1099_);
lean_closure_set(v___f_1122_, 1, v___f_1117_);
lean_closure_set(v___f_1122_, 2, v_inst_1100_);
lean_closure_set(v___f_1122_, 3, v_inst_1097_);
lean_closure_set(v___f_1122_, 4, v_inst_1101_);
lean_closure_set(v___f_1122_, 5, v_inst_1102_);
lean_closure_set(v___f_1122_, 6, v_cls_1119_);
lean_closure_set(v___f_1122_, 7, v_toBind_1103_);
lean_closure_set(v___f_1122_, 8, v___f_1118_);
lean_closure_set(v___f_1122_, 9, v_mod_1104_);
lean_closure_set(v___f_1122_, 10, v_hint_1105_);
lean_closure_set(v___f_1122_, 11, v___x_1120_);
lean_closure_set(v___f_1122_, 12, v___x_1121_);
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1123_, 0, v_toPure_1116_);
lean_closure_set(v___f_1123_, 1, v_cls_1119_);
lean_closure_set(v___f_1123_, 2, v_toBind_1103_);
lean_closure_set(v___f_1123_, 3, v_inst_1108_);
v___x_1124_ = lean_apply_4(v_toBind_1103_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1115_, v___f_1123_);
v___x_1125_ = lean_apply_4(v_toBind_1103_, lean_box(0), lean_box(0), v___x_1124_, v___f_1122_);
return v___x_1125_;
}
else
{
lean_object* v_toPure_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v_inst_1108_);
lean_dec(v_hint_1105_);
lean_dec(v_mod_1104_);
lean_dec(v_toBind_1103_);
lean_dec(v_inst_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec(v_modifyEnv_1099_);
lean_dec_ref(v_inst_1097_);
lean_dec_ref(v_entry_1096_);
v_toPure_1126_ = lean_ctor_get(v_toApplicative_1098_, 1);
lean_inc(v_toPure_1126_);
lean_dec_ref(v_toApplicative_1098_);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_apply_2(v_toPure_1126_, lean_box(0), v___x_1127_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1129_ = _args[0];
lean_object* v___x_1130_ = _args[1];
lean_object* v___x_1131_ = _args[2];
lean_object* v_entry_1132_ = _args[3];
lean_object* v_inst_1133_ = _args[4];
lean_object* v_toApplicative_1134_ = _args[5];
lean_object* v_modifyEnv_1135_ = _args[6];
lean_object* v_inst_1136_ = _args[7];
lean_object* v_inst_1137_ = _args[8];
lean_object* v_inst_1138_ = _args[9];
lean_object* v_toBind_1139_ = _args[10];
lean_object* v_mod_1140_ = _args[11];
lean_object* v_hint_1141_ = _args[12];
lean_object* v_isMeta_1142_ = _args[13];
lean_object* v_isExporting_1143_ = _args[14];
lean_object* v_inst_1144_ = _args[15];
lean_object* v_____do__lift_1145_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1146_; uint8_t v_isExporting_boxed_1147_; lean_object* v_res_1148_; 
v_isMeta_boxed_1146_ = lean_unbox(v_isMeta_1142_);
v_isExporting_boxed_1147_ = lean_unbox(v_isExporting_1143_);
v_res_1148_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v___x_1129_, v___x_1130_, v___x_1131_, v_entry_1132_, v_inst_1133_, v_toApplicative_1134_, v_modifyEnv_1135_, v_inst_1136_, v_inst_1137_, v_inst_1138_, v_toBind_1139_, v_mod_1140_, v_hint_1141_, v_isMeta_boxed_1146_, v_isExporting_boxed_1147_, v_inst_1144_, v_____do__lift_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v_mod_1149_, uint8_t v_isMeta_1150_, lean_object* v___x_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v_inst_1154_, lean_object* v_toApplicative_1155_, lean_object* v_modifyEnv_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_toBind_1160_, lean_object* v_hint_1161_, lean_object* v_inst_1162_, lean_object* v_getEnv_1163_, lean_object* v_____do__lift_1164_){
_start:
{
uint8_t v_isExporting_1165_; lean_object* v_entry_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v_isExporting_1165_ = lean_ctor_get_uint8(v_____do__lift_1164_, sizeof(void*)*8);
lean_inc(v_mod_1149_);
v_entry_1166_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1166_, 0, v_mod_1149_);
lean_ctor_set_uint8(v_entry_1166_, sizeof(void*)*1, v_isExporting_1165_);
lean_ctor_set_uint8(v_entry_1166_, sizeof(void*)*1 + 1, v_isMeta_1150_);
v___x_1167_ = lean_box(v_isMeta_1150_);
v___x_1168_ = lean_box(v_isExporting_1165_);
lean_inc(v_toBind_1160_);
v___f_1169_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1169_, 0, v___x_1151_);
lean_closure_set(v___f_1169_, 1, v___x_1152_);
lean_closure_set(v___f_1169_, 2, v___x_1153_);
lean_closure_set(v___f_1169_, 3, v_entry_1166_);
lean_closure_set(v___f_1169_, 4, v_inst_1154_);
lean_closure_set(v___f_1169_, 5, v_toApplicative_1155_);
lean_closure_set(v___f_1169_, 6, v_modifyEnv_1156_);
lean_closure_set(v___f_1169_, 7, v_inst_1157_);
lean_closure_set(v___f_1169_, 8, v_inst_1158_);
lean_closure_set(v___f_1169_, 9, v_inst_1159_);
lean_closure_set(v___f_1169_, 10, v_toBind_1160_);
lean_closure_set(v___f_1169_, 11, v_mod_1149_);
lean_closure_set(v___f_1169_, 12, v_hint_1161_);
lean_closure_set(v___f_1169_, 13, v___x_1167_);
lean_closure_set(v___f_1169_, 14, v___x_1168_);
lean_closure_set(v___f_1169_, 15, v_inst_1162_);
v___x_1170_ = lean_apply_4(v_toBind_1160_, lean_box(0), lean_box(0), v_getEnv_1163_, v___f_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object* v_mod_1171_, lean_object* v_isMeta_1172_, lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v___x_1175_, lean_object* v_inst_1176_, lean_object* v_toApplicative_1177_, lean_object* v_modifyEnv_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_toBind_1182_, lean_object* v_hint_1183_, lean_object* v_inst_1184_, lean_object* v_getEnv_1185_, lean_object* v_____do__lift_1186_){
_start:
{
uint8_t v_isMeta_boxed_1187_; lean_object* v_res_1188_; 
v_isMeta_boxed_1187_ = lean_unbox(v_isMeta_1172_);
v_res_1188_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v_mod_1171_, v_isMeta_boxed_1187_, v___x_1173_, v___x_1174_, v___x_1175_, v_inst_1176_, v_toApplicative_1177_, v_modifyEnv_1178_, v_inst_1179_, v_inst_1180_, v_inst_1181_, v_toBind_1182_, v_hint_1183_, v_inst_1184_, v_getEnv_1185_, v_____do__lift_1186_);
lean_dec_ref(v_____do__lift_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_mod_1195_, uint8_t v_isMeta_1196_, lean_object* v_hint_1197_){
_start:
{
lean_object* v_toApplicative_1198_; lean_object* v_toBind_1199_; lean_object* v_getEnv_1200_; lean_object* v_modifyEnv_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; 
v_toApplicative_1198_ = lean_ctor_get(v_inst_1189_, 0);
lean_inc_ref(v_toApplicative_1198_);
v_toBind_1199_ = lean_ctor_get(v_inst_1189_, 1);
lean_inc_n(v_toBind_1199_, 2);
v_getEnv_1200_ = lean_ctor_get(v_inst_1190_, 0);
lean_inc_n(v_getEnv_1200_, 2);
v_modifyEnv_1201_ = lean_ctor_get(v_inst_1190_, 1);
lean_inc(v_modifyEnv_1201_);
lean_dec_ref(v_inst_1190_);
v___x_1202_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1203_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1204_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1205_ = lean_box(v_isMeta_1196_);
v___f_1206_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 16, 15);
lean_closure_set(v___f_1206_, 0, v_mod_1195_);
lean_closure_set(v___f_1206_, 1, v___x_1205_);
lean_closure_set(v___f_1206_, 2, v___x_1204_);
lean_closure_set(v___f_1206_, 3, v___x_1202_);
lean_closure_set(v___f_1206_, 4, v___x_1203_);
lean_closure_set(v___f_1206_, 5, v_inst_1191_);
lean_closure_set(v___f_1206_, 6, v_toApplicative_1198_);
lean_closure_set(v___f_1206_, 7, v_modifyEnv_1201_);
lean_closure_set(v___f_1206_, 8, v_inst_1189_);
lean_closure_set(v___f_1206_, 9, v_inst_1193_);
lean_closure_set(v___f_1206_, 10, v_inst_1194_);
lean_closure_set(v___f_1206_, 11, v_toBind_1199_);
lean_closure_set(v___f_1206_, 12, v_hint_1197_);
lean_closure_set(v___f_1206_, 13, v_inst_1192_);
lean_closure_set(v___f_1206_, 14, v_getEnv_1200_);
v___x_1207_ = lean_apply_4(v_toBind_1199_, lean_box(0), lean_box(0), v_getEnv_1200_, v___f_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_mod_1214_, lean_object* v_isMeta_1215_, lean_object* v_hint_1216_){
_start:
{
uint8_t v_isMeta_boxed_1217_; lean_object* v_res_1218_; 
v_isMeta_boxed_1217_ = lean_unbox(v_isMeta_1215_);
v_res_1218_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1208_, v_inst_1209_, v_inst_1210_, v_inst_1211_, v_inst_1212_, v_inst_1213_, v_mod_1214_, v_isMeta_boxed_1217_, v_hint_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_mod_1226_, uint8_t v_isMeta_1227_, lean_object* v_hint_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1220_, v_inst_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_inst_1225_, v_mod_1226_, v_isMeta_1227_, v_hint_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_mod_1237_, lean_object* v_isMeta_1238_, lean_object* v_hint_1239_){
_start:
{
uint8_t v_isMeta_boxed_1240_; lean_object* v_res_1241_; 
v_isMeta_boxed_1240_ = lean_unbox(v_isMeta_1238_);
v_res_1241_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_mod_1237_, v_isMeta_boxed_1240_, v_hint_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, uint8_t v_isMeta_1249_, lean_object* v_toApplicative_1250_, lean_object* v_____do__lift_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = l_Lean_Environment_mainModule(v_____do__lift_1251_);
v___x_1253_ = lean_name_eq(v_modName_1242_, v___x_1252_);
lean_dec(v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v_toApplicative_1250_);
v___x_1254_ = lean_box(0);
v___x_1255_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1243_, v_inst_1244_, v_inst_1245_, v_inst_1246_, v_inst_1247_, v_inst_1248_, v_modName_1242_, v_isMeta_1249_, v___x_1254_);
return v___x_1255_;
}
else
{
lean_object* v_toPure_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v_inst_1248_);
lean_dec_ref(v_inst_1247_);
lean_dec(v_inst_1246_);
lean_dec_ref(v_inst_1245_);
lean_dec_ref(v_inst_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec(v_modName_1242_);
v_toPure_1256_ = lean_ctor_get(v_toApplicative_1250_, 1);
lean_inc(v_toPure_1256_);
lean_dec_ref(v_toApplicative_1250_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_apply_2(v_toPure_1256_, lean_box(0), v___x_1257_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_isMeta_1266_, lean_object* v_toApplicative_1267_, lean_object* v_____do__lift_1268_){
_start:
{
uint8_t v_isMeta_boxed_1269_; lean_object* v_res_1270_; 
v_isMeta_boxed_1269_ = lean_unbox(v_isMeta_1266_);
v_res_1270_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1259_, v_inst_1260_, v_inst_1261_, v_inst_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_isMeta_boxed_1269_, v_toApplicative_1267_, v_____do__lift_1268_);
lean_dec_ref(v_____do__lift_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_modName_1277_, uint8_t v_isMeta_1278_){
_start:
{
lean_object* v_toApplicative_1279_; lean_object* v_toBind_1280_; lean_object* v_getEnv_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; 
v_toApplicative_1279_ = lean_ctor_get(v_inst_1271_, 0);
lean_inc_ref(v_toApplicative_1279_);
v_toBind_1280_ = lean_ctor_get(v_inst_1271_, 1);
lean_inc(v_toBind_1280_);
v_getEnv_1281_ = lean_ctor_get(v_inst_1272_, 0);
lean_inc(v_getEnv_1281_);
v___x_1282_ = lean_box(v_isMeta_1278_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1283_, 0, v_modName_1277_);
lean_closure_set(v___f_1283_, 1, v_inst_1271_);
lean_closure_set(v___f_1283_, 2, v_inst_1272_);
lean_closure_set(v___f_1283_, 3, v_inst_1273_);
lean_closure_set(v___f_1283_, 4, v_inst_1274_);
lean_closure_set(v___f_1283_, 5, v_inst_1275_);
lean_closure_set(v___f_1283_, 6, v_inst_1276_);
lean_closure_set(v___f_1283_, 7, v___x_1282_);
lean_closure_set(v___f_1283_, 8, v_toApplicative_1279_);
v___x_1284_ = lean_apply_4(v_toBind_1280_, lean_box(0), lean_box(0), v_getEnv_1281_, v___f_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_modName_1291_, lean_object* v_isMeta_1292_){
_start:
{
uint8_t v_isMeta_boxed_1293_; lean_object* v_res_1294_; 
v_isMeta_boxed_1293_ = lean_unbox(v_isMeta_1292_);
v_res_1294_ = l_Lean_recordExtraModUse___redArg(v_inst_1285_, v_inst_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v_inst_1290_, v_modName_1291_, v_isMeta_boxed_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_modName_1302_, uint8_t v_isMeta_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_recordExtraModUse___redArg(v_inst_1296_, v_inst_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_inst_1301_, v_modName_1302_, v_isMeta_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_modName_1312_, lean_object* v_isMeta_1313_){
_start:
{
uint8_t v_isMeta_boxed_1314_; lean_object* v_res_1315_; 
v_isMeta_boxed_1314_ = lean_unbox(v_isMeta_1313_);
v_res_1315_ = l_Lean_recordExtraModUse(v_m_1305_, v_inst_1306_, v_inst_1307_, v_inst_1308_, v_inst_1309_, v_inst_1310_, v_inst_1311_, v_modName_1312_, v_isMeta_boxed_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1316_, lean_object* v_____s_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_apply_2(v_toPure_1316_, lean_box(0), v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1320_, lean_object* v_toPure_1321_, lean_object* v_r_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1320_);
v___x_1324_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1325_, lean_object* v___x_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_declName_1333_, lean_object* v_toBind_1334_, lean_object* v___f_1335_, lean_object* v_a_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v_modules_1340_; lean_object* v___x_1341_; lean_object* v_toImport_1342_; lean_object* v_module_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1339_ = l_Lean_Environment_header(v_env_1325_);
v_modules_1340_ = lean_ctor_get(v___x_1339_, 3);
lean_inc_ref(v_modules_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_array_get(v___x_1326_, v_modules_1340_, v_a_1336_);
lean_dec_ref(v_modules_1340_);
v_toImport_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_ref(v_toImport_1342_);
lean_dec(v___x_1341_);
v_module_1343_ = lean_ctor_get(v_toImport_1342_, 0);
lean_inc(v_module_1343_);
lean_dec_ref(v_toImport_1342_);
v___x_1344_ = 0;
v___x_1345_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_module_1343_, v___x_1344_, v_declName_1333_);
v___x_1346_ = lean_apply_4(v_toBind_1334_, lean_box(0), lean_box(0), v___x_1345_, v___f_1335_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1347_, lean_object* v___x_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_declName_1355_, lean_object* v_toBind_1356_, lean_object* v___f_1357_, lean_object* v_a_1358_, lean_object* v_x_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1347_, v___x_1348_, v_inst_1349_, v_inst_1350_, v_inst_1351_, v_inst_1352_, v_inst_1353_, v_inst_1354_, v_declName_1355_, v_toBind_1356_, v___f_1357_, v_a_1358_, v_x_1359_, v___y_1360_);
lean_dec(v_a_1358_);
lean_dec_ref(v___x_1348_);
lean_dec_ref(v_env_1347_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1362_, lean_object* v_env_1363_, lean_object* v___x_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_inst_1370_, lean_object* v_declName_1371_, lean_object* v_toBind_1372_, lean_object* v___f_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v___x_1376_, lean_object* v_____r_1377_){
_start:
{
lean_object* v___y_1379_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1387_ = l_Lean_indirectModUseExt;
v___x_1388_ = lean_box(1);
v___x_1389_ = lean_box(0);
lean_inc_ref(v_env_1363_);
v___x_1390_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1374_, v___x_1387_, v_env_1363_, v___x_1388_, v___x_1389_);
lean_inc(v_declName_1371_);
v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1375_, v___x_1376_, v___x_1390_, v_declName_1371_);
lean_dec(v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1379_ = v___x_1392_;
goto v___jp_1378_;
}
else
{
lean_object* v_val_1393_; 
v_val_1393_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v___x_1391_, 1);
v___y_1379_ = v_val_1393_;
goto v___jp_1378_;
}
v___jp_1378_:
{
lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; size_t v_sz_1383_; size_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1380_ = lean_box(0);
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1381_, 0, v___x_1380_);
lean_closure_set(v___f_1381_, 1, v_toPure_1362_);
lean_inc(v_toBind_1372_);
lean_inc_ref(v_inst_1365_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1382_, 0, v_env_1363_);
lean_closure_set(v___f_1382_, 1, v___x_1364_);
lean_closure_set(v___f_1382_, 2, v_inst_1365_);
lean_closure_set(v___f_1382_, 3, v_inst_1366_);
lean_closure_set(v___f_1382_, 4, v_inst_1367_);
lean_closure_set(v___f_1382_, 5, v_inst_1368_);
lean_closure_set(v___f_1382_, 6, v_inst_1369_);
lean_closure_set(v___f_1382_, 7, v_inst_1370_);
lean_closure_set(v___f_1382_, 8, v_declName_1371_);
lean_closure_set(v___f_1382_, 9, v_toBind_1372_);
lean_closure_set(v___f_1382_, 10, v___f_1381_);
v_sz_1383_ = lean_array_size(v___y_1379_);
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1365_, v___y_1379_, v___f_1382_, v_sz_1383_, v___x_1384_, v___x_1380_);
v___x_1386_ = lean_apply_4(v_toBind_1372_, lean_box(0), lean_box(0), v___x_1385_, v___f_1373_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_declName_1401_, lean_object* v_toBind_1402_, lean_object* v___f_1403_, uint8_t v_isMeta_1404_, lean_object* v_____do__lift_1405_){
_start:
{
uint8_t v___y_1407_; 
if (v_isMeta_1404_ == 0)
{
lean_dec_ref(v_____do__lift_1405_);
v___y_1407_ = v_isMeta_1404_;
goto v___jp_1406_;
}
else
{
uint8_t v___x_1412_; 
lean_inc(v_declName_1401_);
v___x_1412_ = l_Lean_isMarkedMeta(v_____do__lift_1405_, v_declName_1401_);
if (v___x_1412_ == 0)
{
v___y_1407_ = v_isMeta_1404_;
goto v___jp_1406_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = 0;
v___y_1407_ = v___x_1413_;
goto v___jp_1406_;
}
}
v___jp_1406_:
{
lean_object* v_toImport_1408_; lean_object* v_module_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_toImport_1408_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_toImport_1408_);
lean_dec_ref(v___x_1394_);
v_module_1409_ = lean_ctor_get(v_toImport_1408_, 0);
lean_inc(v_module_1409_);
lean_dec_ref(v_toImport_1408_);
v___x_1410_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1395_, v_inst_1396_, v_inst_1397_, v_inst_1398_, v_inst_1399_, v_inst_1400_, v_module_1409_, v___y_1407_, v_declName_1401_);
v___x_1411_ = lean_apply_4(v_toBind_1402_, lean_box(0), lean_box(0), v___x_1410_, v___f_1403_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_declName_1421_, lean_object* v_toBind_1422_, lean_object* v___f_1423_, lean_object* v_isMeta_1424_, lean_object* v_____do__lift_1425_){
_start:
{
uint8_t v_isMeta_boxed_1426_; lean_object* v_res_1427_; 
v_isMeta_boxed_1426_ = lean_unbox(v_isMeta_1424_);
v_res_1427_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1414_, v_inst_1415_, v_inst_1416_, v_inst_1417_, v_inst_1418_, v_inst_1419_, v_inst_1420_, v_declName_1421_, v_toBind_1422_, v___f_1423_, v_isMeta_boxed_1426_, v_____do__lift_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1428_, lean_object* v_declName_1429_, lean_object* v___x_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_toBind_1437_, lean_object* v___f_1438_, lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, uint8_t v_isMeta_1442_, lean_object* v_getEnv_1443_, lean_object* v_env_1444_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1444_, v_declName_1429_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref(v_env_1444_);
lean_dec(v_getEnv_1443_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v___x_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v___f_1438_);
lean_dec(v_toBind_1437_);
lean_dec(v_inst_1436_);
lean_dec_ref(v_inst_1435_);
lean_dec(v_inst_1434_);
lean_dec_ref(v_inst_1433_);
lean_dec_ref(v_inst_1432_);
lean_dec_ref(v_inst_1431_);
lean_dec_ref(v___x_1430_);
lean_dec(v_declName_1429_);
goto v___jp_1445_;
}
else
{
lean_object* v_val_1449_; lean_object* v___x_1450_; lean_object* v_modules_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_val_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = l_Lean_Environment_header(v_env_1444_);
v_modules_1451_ = lean_ctor_get(v___x_1450_, 3);
lean_inc_ref(v_modules_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = lean_array_get_size(v_modules_1451_);
v___x_1453_ = lean_nat_dec_lt(v_val_1449_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_dec_ref(v_modules_1451_);
lean_dec(v_val_1449_);
lean_dec_ref(v_env_1444_);
lean_dec(v_getEnv_1443_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v___x_1440_);
lean_dec_ref(v___x_1439_);
lean_dec(v___f_1438_);
lean_dec(v_toBind_1437_);
lean_dec(v_inst_1436_);
lean_dec_ref(v_inst_1435_);
lean_dec(v_inst_1434_);
lean_dec_ref(v_inst_1433_);
lean_dec_ref(v_inst_1432_);
lean_dec_ref(v_inst_1431_);
lean_dec_ref(v___x_1430_);
lean_dec(v_declName_1429_);
goto v___jp_1445_;
}
else
{
lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; 
lean_inc_n(v_toBind_1437_, 2);
lean_inc(v_declName_1429_);
lean_inc(v_inst_1436_);
lean_inc_ref(v_inst_1435_);
lean_inc(v_inst_1434_);
lean_inc_ref(v_inst_1433_);
lean_inc_ref(v_inst_1432_);
lean_inc_ref(v_inst_1431_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1454_, 0, v_toPure_1428_);
lean_closure_set(v___f_1454_, 1, v_env_1444_);
lean_closure_set(v___f_1454_, 2, v___x_1430_);
lean_closure_set(v___f_1454_, 3, v_inst_1431_);
lean_closure_set(v___f_1454_, 4, v_inst_1432_);
lean_closure_set(v___f_1454_, 5, v_inst_1433_);
lean_closure_set(v___f_1454_, 6, v_inst_1434_);
lean_closure_set(v___f_1454_, 7, v_inst_1435_);
lean_closure_set(v___f_1454_, 8, v_inst_1436_);
lean_closure_set(v___f_1454_, 9, v_declName_1429_);
lean_closure_set(v___f_1454_, 10, v_toBind_1437_);
lean_closure_set(v___f_1454_, 11, v___f_1438_);
lean_closure_set(v___f_1454_, 12, v___x_1439_);
lean_closure_set(v___f_1454_, 13, v___x_1440_);
lean_closure_set(v___f_1454_, 14, v___x_1441_);
v___x_1455_ = lean_array_fget(v_modules_1451_, v_val_1449_);
lean_dec(v_val_1449_);
lean_dec_ref(v_modules_1451_);
v___x_1456_ = lean_box(v_isMeta_1442_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1457_, 0, v___x_1455_);
lean_closure_set(v___f_1457_, 1, v_inst_1431_);
lean_closure_set(v___f_1457_, 2, v_inst_1432_);
lean_closure_set(v___f_1457_, 3, v_inst_1433_);
lean_closure_set(v___f_1457_, 4, v_inst_1434_);
lean_closure_set(v___f_1457_, 5, v_inst_1435_);
lean_closure_set(v___f_1457_, 6, v_inst_1436_);
lean_closure_set(v___f_1457_, 7, v_declName_1429_);
lean_closure_set(v___f_1457_, 8, v_toBind_1437_);
lean_closure_set(v___f_1457_, 9, v___f_1454_);
lean_closure_set(v___f_1457_, 10, v___x_1456_);
v___x_1458_ = lean_apply_4(v_toBind_1437_, lean_box(0), lean_box(0), v_getEnv_1443_, v___f_1457_);
return v___x_1458_;
}
}
v___jp_1445_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = lean_apply_2(v_toPure_1428_, lean_box(0), v___x_1446_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1459_ = _args[0];
lean_object* v_declName_1460_ = _args[1];
lean_object* v___x_1461_ = _args[2];
lean_object* v_inst_1462_ = _args[3];
lean_object* v_inst_1463_ = _args[4];
lean_object* v_inst_1464_ = _args[5];
lean_object* v_inst_1465_ = _args[6];
lean_object* v_inst_1466_ = _args[7];
lean_object* v_inst_1467_ = _args[8];
lean_object* v_toBind_1468_ = _args[9];
lean_object* v___f_1469_ = _args[10];
lean_object* v___x_1470_ = _args[11];
lean_object* v___x_1471_ = _args[12];
lean_object* v___x_1472_ = _args[13];
lean_object* v_isMeta_1473_ = _args[14];
lean_object* v_getEnv_1474_ = _args[15];
lean_object* v_env_1475_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1476_; lean_object* v_res_1477_; 
v_isMeta_boxed_1476_ = lean_unbox(v_isMeta_1473_);
v_res_1477_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1459_, v_declName_1460_, v___x_1461_, v_inst_1462_, v_inst_1463_, v_inst_1464_, v_inst_1465_, v_inst_1466_, v_inst_1467_, v_toBind_1468_, v___f_1469_, v___x_1470_, v___x_1471_, v___x_1472_, v_isMeta_boxed_1476_, v_getEnv_1474_, v_env_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_declName_1484_, uint8_t v_isMeta_1485_){
_start:
{
lean_object* v_toApplicative_1486_; lean_object* v_toBind_1487_; lean_object* v_getEnv_1488_; lean_object* v_toPure_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; 
v_toApplicative_1486_ = lean_ctor_get(v_inst_1478_, 0);
v_toBind_1487_ = lean_ctor_get(v_inst_1478_, 1);
lean_inc_n(v_toBind_1487_, 2);
v_getEnv_1488_ = lean_ctor_get(v_inst_1479_, 0);
lean_inc_n(v_getEnv_1488_, 2);
v_toPure_1489_ = lean_ctor_get(v_toApplicative_1486_, 1);
lean_inc_n(v_toPure_1489_, 2);
v___x_1490_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1491_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1492_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1493_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1494_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1494_, 0, v_toPure_1489_);
v___x_1495_ = lean_box(v_isMeta_1485_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1496_, 0, v_toPure_1489_);
lean_closure_set(v___f_1496_, 1, v_declName_1484_);
lean_closure_set(v___f_1496_, 2, v___x_1493_);
lean_closure_set(v___f_1496_, 3, v_inst_1478_);
lean_closure_set(v___f_1496_, 4, v_inst_1479_);
lean_closure_set(v___f_1496_, 5, v_inst_1480_);
lean_closure_set(v___f_1496_, 6, v_inst_1481_);
lean_closure_set(v___f_1496_, 7, v_inst_1482_);
lean_closure_set(v___f_1496_, 8, v_inst_1483_);
lean_closure_set(v___f_1496_, 9, v_toBind_1487_);
lean_closure_set(v___f_1496_, 10, v___f_1494_);
lean_closure_set(v___f_1496_, 11, v___x_1492_);
lean_closure_set(v___f_1496_, 12, v___x_1490_);
lean_closure_set(v___f_1496_, 13, v___x_1491_);
lean_closure_set(v___f_1496_, 14, v___x_1495_);
lean_closure_set(v___f_1496_, 15, v_getEnv_1488_);
v___x_1497_ = lean_apply_4(v_toBind_1487_, lean_box(0), lean_box(0), v_getEnv_1488_, v___f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_declName_1504_, lean_object* v_isMeta_1505_){
_start:
{
uint8_t v_isMeta_boxed_1506_; lean_object* v_res_1507_; 
v_isMeta_boxed_1506_ = lean_unbox(v_isMeta_1505_);
v_res_1507_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1498_, v_inst_1499_, v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_declName_1504_, v_isMeta_boxed_1506_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_declName_1515_, uint8_t v_isMeta_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_inst_1513_, v_inst_1514_, v_declName_1515_, v_isMeta_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_declName_1525_, lean_object* v_isMeta_1526_){
_start:
{
uint8_t v_isMeta_boxed_1527_; lean_object* v_res_1528_; 
v_isMeta_boxed_1527_ = lean_unbox(v_isMeta_1526_);
v_res_1528_ = l_Lean_recordExtraModUseFromDecl(v_m_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_declName_1525_, v_isMeta_boxed_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1529_, lean_object* v_e_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_box(0);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1534_);
lean_dec_ref(v_x_1534_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_array_mk(v_es_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1554_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1556_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1560_, lean_object* v_modIdx_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1562_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1563_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1564_ = 0;
v___x_1565_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1562_, v___x_1563_, v_env_1560_, v_modIdx_1561_, v___x_1564_);
v___x_1566_ = lean_array_get_size(v___x_1565_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_nat_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
uint8_t v___x_1569_; 
v___x_1569_ = 1;
return v___x_1569_;
}
else
{
uint8_t v___x_1570_; 
v___x_1570_ = 0;
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1571_, lean_object* v_modIdx_1572_){
_start:
{
uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_res_1573_ = l_Lean_isExtraRevModUse(v_env_1571_, v_modIdx_1572_);
lean_dec(v_modIdx_1572_);
lean_dec_ref(v_env_1571_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v_toEnvExtension_1577_; lean_object* v_asyncMode_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_toEnvExtension_1577_ = lean_ctor_get(v___x_1575_, 0);
v_asyncMode_1578_ = lean_ctor_get(v_toEnvExtension_1577_, 2);
lean_inc(v_asyncMode_1578_);
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1575_, v_x_1576_, v___x_1579_, v_asyncMode_1578_, v___x_1580_);
lean_dec(v_asyncMode_1578_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v_modifyEnv_1585_, lean_object* v___f_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_cls_1591_, lean_object* v_toBind_1592_, lean_object* v___f_1593_, uint8_t v_____do__lift_1594_){
_start:
{
if (v_____do__lift_1594_ == 0)
{
lean_object* v___x_1595_; 
lean_dec(v___f_1593_);
lean_dec(v_toBind_1592_);
lean_dec(v_cls_1591_);
lean_dec(v_inst_1590_);
lean_dec_ref(v_inst_1589_);
lean_dec_ref(v_inst_1588_);
lean_dec_ref(v_inst_1587_);
v___x_1595_ = lean_apply_1(v_modifyEnv_1585_, v___f_1586_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec_ref(v___f_1586_);
lean_dec(v_modifyEnv_1585_);
v___x_1596_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1);
v___x_1597_ = l_Lean_addTrace___redArg(v_inst_1587_, v_inst_1588_, v_inst_1589_, v_inst_1590_, v_cls_1591_, v___x_1596_);
v___x_1598_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1597_, v___f_1593_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object* v_modifyEnv_1599_, lean_object* v___f_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_cls_1605_, lean_object* v_toBind_1606_, lean_object* v___f_1607_, lean_object* v_____do__lift_1608_){
_start:
{
uint8_t v_____do__lift_328__boxed_1609_; lean_object* v_res_1610_; 
v_____do__lift_328__boxed_1609_ = lean_unbox(v_____do__lift_1608_);
v_res_1610_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(v_modifyEnv_1599_, v___f_1600_, v_inst_1601_, v_inst_1602_, v_inst_1603_, v_inst_1604_, v_cls_1605_, v_toBind_1606_, v___f_1607_, v_____do__lift_328__boxed_1609_);
return v_res_1610_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___f_1612_; 
v___x_1611_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1612_, 0, v___x_1611_);
return v___f_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v___x_1613_, lean_object* v_toApplicative_1614_, lean_object* v_inst_1615_, lean_object* v_modifyEnv_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_toBind_1620_, lean_object* v_inst_1621_, lean_object* v_____do__lift_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1623_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1624_ = lean_box(1);
v___x_1625_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1613_, v___x_1623_, v_____do__lift_1622_, v___x_1624_);
v___x_1626_ = l_List_isEmpty___redArg(v___x_1625_);
lean_dec(v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v_toPure_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_inst_1621_);
lean_dec(v_toBind_1620_);
lean_dec(v_inst_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec_ref(v_inst_1617_);
lean_dec(v_modifyEnv_1616_);
lean_dec_ref(v_inst_1615_);
v_toPure_1627_ = lean_ctor_get(v_toApplicative_1614_, 1);
lean_inc(v_toPure_1627_);
lean_dec_ref(v_toApplicative_1614_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_apply_2(v_toPure_1627_, lean_box(0), v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v_getInheritedTraceOptions_1630_; lean_object* v_toPure_1631_; lean_object* v___f_1632_; lean_object* v___f_1633_; lean_object* v_cls_1634_; lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_getInheritedTraceOptions_1630_ = lean_ctor_get(v_inst_1615_, 2);
lean_inc(v_getInheritedTraceOptions_1630_);
v_toPure_1631_ = lean_ctor_get(v_toApplicative_1614_, 1);
lean_inc(v_toPure_1631_);
lean_dec_ref(v_toApplicative_1614_);
v___f_1632_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0);
lean_inc(v_modifyEnv_1616_);
v___f_1633_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1633_, 0, v_modifyEnv_1616_);
lean_closure_set(v___f_1633_, 1, v___f_1632_);
v_cls_1634_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1620_, 3);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1635_, 0, v_modifyEnv_1616_);
lean_closure_set(v___f_1635_, 1, v___f_1632_);
lean_closure_set(v___f_1635_, 2, v_inst_1617_);
lean_closure_set(v___f_1635_, 3, v_inst_1615_);
lean_closure_set(v___f_1635_, 4, v_inst_1618_);
lean_closure_set(v___f_1635_, 5, v_inst_1619_);
lean_closure_set(v___f_1635_, 6, v_cls_1634_);
lean_closure_set(v___f_1635_, 7, v_toBind_1620_);
lean_closure_set(v___f_1635_, 8, v___f_1633_);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1636_, 0, v_toPure_1631_);
lean_closure_set(v___f_1636_, 1, v_cls_1634_);
lean_closure_set(v___f_1636_, 2, v_toBind_1620_);
lean_closure_set(v___f_1636_, 3, v_inst_1621_);
v___x_1637_ = lean_apply_4(v_toBind_1620_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1630_, v___f_1636_);
v___x_1638_ = lean_apply_4(v_toBind_1620_, lean_box(0), lean_box(0), v___x_1637_, v___f_1635_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_){
_start:
{
lean_object* v_toApplicative_1645_; lean_object* v_toBind_1646_; lean_object* v_getEnv_1647_; lean_object* v_modifyEnv_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; 
v_toApplicative_1645_ = lean_ctor_get(v_inst_1639_, 0);
lean_inc_ref(v_toApplicative_1645_);
v_toBind_1646_ = lean_ctor_get(v_inst_1639_, 1);
lean_inc_n(v_toBind_1646_, 2);
v_getEnv_1647_ = lean_ctor_get(v_inst_1640_, 0);
lean_inc(v_getEnv_1647_);
v_modifyEnv_1648_ = lean_ctor_get(v_inst_1640_, 1);
lean_inc(v_modifyEnv_1648_);
lean_dec_ref(v_inst_1640_);
v___x_1649_ = lean_box(0);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4), 10, 9);
lean_closure_set(v___f_1650_, 0, v___x_1649_);
lean_closure_set(v___f_1650_, 1, v_toApplicative_1645_);
lean_closure_set(v___f_1650_, 2, v_inst_1641_);
lean_closure_set(v___f_1650_, 3, v_modifyEnv_1648_);
lean_closure_set(v___f_1650_, 4, v_inst_1639_);
lean_closure_set(v___f_1650_, 5, v_inst_1643_);
lean_closure_set(v___f_1650_, 6, v_inst_1644_);
lean_closure_set(v___f_1650_, 7, v_toBind_1646_);
lean_closure_set(v___f_1650_, 8, v_inst_1642_);
v___x_1651_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v_getEnv_1647_, v___f_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_inst_1657_, v_inst_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_unsigned_to_nat(4259277863u);
v___x_1675_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1676_ = l_Lean_Name_num___override(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1679_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1680_ = l_Lean_Name_str___override(v___x_1679_, v___x_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1683_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1684_ = l_Lean_Name_str___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_unsigned_to_nat(2u);
v___x_1686_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1687_ = l_Lean_Name_num___override(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1689_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1690_ = 0;
v___x_1691_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1692_ = l_Lean_registerTraceClass(v___x_1689_, v___x_1690_, v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1694_;
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
