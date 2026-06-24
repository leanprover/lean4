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
uint8_t v_____do__lift_579__boxed_381_; lean_object* v_res_382_; 
v_____do__lift_579__boxed_381_ = lean_unbox(v_____do__lift_380_);
v_res_382_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_modifyEnv_369_, v___f_370_, v_declName_371_, v_kind_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_cls_377_, v_toBind_378_, v___f_379_, v_____do__lift_579__boxed_381_);
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
lean_dec_ref_known(v___x_429_, 2);
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
v___x_504_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_597_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_entries_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_608_ = lean_array_mk(v_entries_606_);
v___x_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_entries_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_610_, v_x_611_, v_entries_612_);
lean_dec_ref(v_x_611_);
lean_dec_ref(v_x_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_mk(v_es_614_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_box(0));
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_619_);
lean_dec_ref(v_x_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_651_, lean_object* v_k_652_, lean_object* v_v_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_651_, v___x_654_, v_k_652_, v_v_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_657_, size_t v_x_658_, size_t v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_es_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v_j_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_es_662_ = lean_ctor_get(v_x_657_, 0);
v___x_663_ = ((size_t)31ULL);
v___x_664_ = lean_usize_land(v_x_658_, v___x_663_);
v_j_665_ = lean_usize_to_nat(v___x_664_);
v___x_666_ = lean_array_get_size(v_es_662_);
v___x_667_ = lean_nat_dec_lt(v_j_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec(v_j_665_);
lean_dec(v_x_661_);
lean_dec_ref(v_x_660_);
return v_x_657_;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_706_; 
lean_inc_ref(v_es_662_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_x_657_, 0);
lean_dec(v_unused_707_);
v___x_669_ = v_x_657_;
v_isShared_670_ = v_isSharedCheck_706_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_x_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_706_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_v_671_; lean_object* v___x_672_; lean_object* v_xs_x27_673_; lean_object* v___y_675_; 
v_v_671_ = lean_array_fget(v_es_662_, v_j_665_);
v___x_672_ = lean_box(0);
v_xs_x27_673_ = lean_array_fset(v_es_662_, v_j_665_, v___x_672_);
switch(lean_obj_tag(v_v_671_))
{
case 0:
{
lean_object* v_key_680_; lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_691_; 
v_key_680_ = lean_ctor_get(v_v_671_, 0);
v_val_681_ = lean_ctor_get(v_v_671_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_v_671_);
if (v_isSharedCheck_691_ == 0)
{
v___x_683_ = v_v_671_;
v_isShared_684_ = v_isSharedCheck_691_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_inc(v_key_680_);
lean_dec(v_v_671_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_691_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_instBEqExtraModUse_beq(v_x_660_, v_key_680_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_del_object(v___x_683_);
v___x_686_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_680_, v_val_681_, v_x_660_, v_x_661_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___y_675_ = v___x_687_;
goto v___jp_674_;
}
else
{
lean_object* v___x_689_; 
lean_dec(v_val_681_);
lean_dec(v_key_680_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v_x_661_);
lean_ctor_set(v___x_683_, 0, v_x_660_);
v___x_689_ = v___x_683_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_x_660_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_x_661_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v___y_675_ = v___x_689_;
goto v___jp_674_;
}
}
}
}
case 1:
{
lean_object* v_node_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_704_; 
v_node_692_ = lean_ctor_get(v_v_671_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_v_671_);
if (v_isSharedCheck_704_ == 0)
{
v___x_694_ = v_v_671_;
v_isShared_695_ = v_isSharedCheck_704_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_node_692_);
lean_dec(v_v_671_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_704_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_696_ = ((size_t)5ULL);
v___x_697_ = lean_usize_shift_right(v_x_658_, v___x_696_);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_x_659_, v___x_698_);
v___x_700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_692_, v___x_697_, v___x_699_, v_x_660_, v_x_661_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_700_);
v___x_702_ = v___x_694_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v___y_675_ = v___x_702_;
goto v___jp_674_;
}
}
}
default: 
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_x_660_);
lean_ctor_set(v___x_705_, 1, v_x_661_);
v___y_675_ = v___x_705_;
goto v___jp_674_;
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_array_fset(v_xs_x27_673_, v_j_665_, v___y_675_);
lean_dec(v_j_665_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_676_);
v___x_678_ = v___x_669_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
else
{
lean_object* v_ks_708_; lean_object* v_vs_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_729_; 
v_ks_708_ = lean_ctor_get(v_x_657_, 0);
v_vs_709_ = lean_ctor_get(v_x_657_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_729_ == 0)
{
v___x_711_ = v_x_657_;
v_isShared_712_ = v_isSharedCheck_729_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_vs_709_);
lean_inc(v_ks_708_);
lean_dec(v_x_657_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_729_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_ks_708_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_vs_709_);
v___x_714_ = v_reuseFailAlloc_728_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v_newNode_715_; uint8_t v___y_717_; size_t v___x_723_; uint8_t v___x_724_; 
v_newNode_715_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_714_, v_x_660_, v_x_661_);
v___x_723_ = ((size_t)7ULL);
v___x_724_ = lean_usize_dec_le(v___x_723_, v_x_659_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_715_);
v___x_726_ = lean_unsigned_to_nat(4u);
v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
v___y_717_ = v___x_727_;
goto v___jp_716_;
}
else
{
v___y_717_ = v___x_724_;
goto v___jp_716_;
}
v___jp_716_:
{
if (v___y_717_ == 0)
{
lean_object* v_ks_718_; lean_object* v_vs_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_ks_718_ = lean_ctor_get(v_newNode_715_, 0);
lean_inc_ref(v_ks_718_);
v_vs_719_ = lean_ctor_get(v_newNode_715_, 1);
lean_inc_ref(v_vs_719_);
lean_dec_ref(v_newNode_715_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_659_, v_ks_718_, v_vs_719_, v___x_720_, v___x_721_);
lean_dec_ref(v_vs_719_);
lean_dec_ref(v_ks_718_);
return v___x_722_;
}
else
{
return v_newNode_715_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_730_, lean_object* v_keys_731_, lean_object* v_vals_732_, lean_object* v_i_733_, lean_object* v_entries_734_){
_start:
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_array_get_size(v_keys_731_);
v___x_736_ = lean_nat_dec_lt(v_i_733_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_i_733_);
return v_entries_734_;
}
else
{
lean_object* v_k_737_; lean_object* v_v_738_; uint64_t v___x_739_; size_t v_h_740_; size_t v___x_741_; lean_object* v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v_h_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_k_737_ = lean_array_fget_borrowed(v_keys_731_, v_i_733_);
v_v_738_ = lean_array_fget_borrowed(v_vals_732_, v_i_733_);
v___x_739_ = l_Lean_instHashableExtraModUse_hash(v_k_737_);
v_h_740_ = lean_uint64_to_usize(v___x_739_);
v___x_741_ = ((size_t)5ULL);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v_depth_730_, v___x_743_);
v___x_745_ = lean_usize_mul(v___x_741_, v___x_744_);
v_h_746_ = lean_usize_shift_right(v_h_740_, v___x_745_);
v___x_747_ = lean_nat_add(v_i_733_, v___x_742_);
lean_dec(v_i_733_);
lean_inc(v_v_738_);
lean_inc(v_k_737_);
v___x_748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_734_, v_h_746_, v_depth_730_, v_k_737_, v_v_738_);
v_i_733_ = v___x_747_;
v_entries_734_ = v___x_748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_750_, lean_object* v_keys_751_, lean_object* v_vals_752_, lean_object* v_i_753_, lean_object* v_entries_754_){
_start:
{
size_t v_depth_boxed_755_; lean_object* v_res_756_; 
v_depth_boxed_755_ = lean_unbox_usize(v_depth_750_);
lean_dec(v_depth_750_);
v_res_756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_755_, v_keys_751_, v_vals_752_, v_i_753_, v_entries_754_);
lean_dec_ref(v_vals_752_);
lean_dec_ref(v_keys_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
size_t v_x_567__boxed_762_; size_t v_x_568__boxed_763_; lean_object* v_res_764_; 
v_x_567__boxed_762_ = lean_unbox_usize(v_x_758_);
lean_dec(v_x_758_);
v_x_568__boxed_763_ = lean_unbox_usize(v_x_759_);
lean_dec(v_x_759_);
v_res_764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_757_, v_x_567__boxed_762_, v_x_568__boxed_763_, v_x_760_, v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
uint64_t v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_768_ = l_Lean_instHashableExtraModUse_hash(v_x_766_);
v___x_769_ = lean_uint64_to_usize(v___x_768_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_765_, v___x_769_, v___x_770_, v_x_766_, v_x_767_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_772_, lean_object* v_k_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_box(0);
v___x_775_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_772_, v_k_773_, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_776_, lean_object* v_i_777_, lean_object* v_k_778_){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_array_get_size(v_keys_776_);
v___x_780_ = lean_nat_dec_lt(v_i_777_, v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v_i_777_);
return v___x_780_;
}
else
{
lean_object* v_k_x27_781_; uint8_t v___x_782_; 
v_k_x27_781_ = lean_array_fget_borrowed(v_keys_776_, v_i_777_);
v___x_782_ = l_Lean_instBEqExtraModUse_beq(v_k_778_, v_k_x27_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_i_777_, v___x_783_);
lean_dec(v_i_777_);
v_i_777_ = v___x_784_;
goto _start;
}
else
{
lean_dec(v_i_777_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_786_, lean_object* v_i_787_, lean_object* v_k_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_786_, v_i_787_, v_k_788_);
lean_dec_ref(v_k_788_);
lean_dec_ref(v_keys_786_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_791_, size_t v_x_792_, lean_object* v_x_793_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
lean_object* v_es_794_; lean_object* v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v_j_798_; lean_object* v___x_799_; 
v_es_794_ = lean_ctor_get(v_x_791_, 0);
v___x_795_ = lean_box(2);
v___x_796_ = ((size_t)31ULL);
v___x_797_ = lean_usize_land(v_x_792_, v___x_796_);
v_j_798_ = lean_usize_to_nat(v___x_797_);
v___x_799_ = lean_array_get_borrowed(v___x_795_, v_es_794_, v_j_798_);
lean_dec(v_j_798_);
switch(lean_obj_tag(v___x_799_))
{
case 0:
{
lean_object* v_key_800_; uint8_t v___x_801_; 
v_key_800_ = lean_ctor_get(v___x_799_, 0);
v___x_801_ = l_Lean_instBEqExtraModUse_beq(v_x_793_, v_key_800_);
return v___x_801_;
}
case 1:
{
lean_object* v_node_802_; size_t v___x_803_; size_t v___x_804_; 
v_node_802_ = lean_ctor_get(v___x_799_, 0);
v___x_803_ = ((size_t)5ULL);
v___x_804_ = lean_usize_shift_right(v_x_792_, v___x_803_);
v_x_791_ = v_node_802_;
v_x_792_ = v___x_804_;
goto _start;
}
default: 
{
uint8_t v___x_806_; 
v___x_806_ = 0;
return v___x_806_;
}
}
}
else
{
lean_object* v_ks_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_ks_807_ = lean_ctor_get(v_x_791_, 0);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_807_, v___x_808_, v_x_793_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
size_t v_x_753__boxed_813_; uint8_t v_res_814_; lean_object* v_r_815_; 
v_x_753__boxed_813_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_814_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_810_, v_x_753__boxed_813_, v_x_812_);
lean_dec_ref(v_x_812_);
lean_dec_ref(v_x_810_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint64_t v___x_818_; size_t v___x_819_; uint8_t v___x_820_; 
v___x_818_ = l_Lean_instHashableExtraModUse_hash(v_x_817_);
v___x_819_ = lean_uint64_to_usize(v___x_818_);
v___x_820_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_816_, v___x_819_, v_x_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_821_, v_x_822_);
lean_dec_ref(v_x_822_);
lean_dec_ref(v_x_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_867_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_869_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_874_, v_x_875_, v_x_876_);
lean_dec_ref(v_x_876_);
lean_dec_ref(v_x_875_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_880_, v_x_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, size_t v_x_886_, lean_object* v_x_887_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_885_, v_x_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
size_t v_x_951__boxed_893_; uint8_t v_res_894_; lean_object* v_r_895_; 
v_x_951__boxed_893_ = lean_unbox_usize(v_x_891_);
lean_dec(v_x_891_);
v_res_894_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_889_, v_x_890_, v_x_951__boxed_893_, v_x_892_);
lean_dec_ref(v_x_892_);
lean_dec_ref(v_x_890_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_896_, lean_object* v_x_897_, size_t v_x_898_, size_t v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_897_, v_x_898_, v_x_899_, v_x_900_, v_x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
size_t v_x_962__boxed_909_; size_t v_x_963__boxed_910_; lean_object* v_res_911_; 
v_x_962__boxed_909_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_x_963__boxed_910_ = lean_unbox_usize(v_x_906_);
lean_dec(v_x_906_);
v_res_911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_903_, v_x_904_, v_x_962__boxed_909_, v_x_963__boxed_910_, v_x_907_, v_x_908_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_912_, lean_object* v_keys_913_, lean_object* v_vals_914_, lean_object* v_heq_915_, lean_object* v_i_916_, lean_object* v_k_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_913_, v_i_916_, v_k_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_919_, lean_object* v_keys_920_, lean_object* v_vals_921_, lean_object* v_heq_922_, lean_object* v_i_923_, lean_object* v_k_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_919_, v_keys_920_, v_vals_921_, v_heq_922_, v_i_923_, v_k_924_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_vals_921_);
lean_dec_ref(v_keys_920_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_927_, lean_object* v_n_928_, lean_object* v_k_929_, lean_object* v_v_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_928_, v_k_929_, v_v_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_932_, size_t v_depth_933_, lean_object* v_keys_934_, lean_object* v_vals_935_, lean_object* v_heq_936_, lean_object* v_i_937_, lean_object* v_entries_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_933_, v_keys_934_, v_vals_935_, v_i_937_, v_entries_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_940_, lean_object* v_depth_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_heq_944_, lean_object* v_i_945_, lean_object* v_entries_946_){
_start:
{
size_t v_depth_boxed_947_; lean_object* v_res_948_; 
v_depth_boxed_947_ = lean_unbox_usize(v_depth_941_);
lean_dec(v_depth_941_);
v_res_948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_940_, v_depth_boxed_947_, v_keys_942_, v_vals_943_, v_heq_944_, v_i_945_, v_entries_946_);
lean_dec_ref(v_vals_943_);
lean_dec_ref(v_keys_942_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_950_, v_x_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_956_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_957_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_956_, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_961_, lean_object* v_modIdx_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; 
v___x_963_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_964_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_965_ = 0;
v___x_966_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_963_, v___x_964_, v_env_961_, v_modIdx_962_, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_967_, lean_object* v_modIdx_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_getExtraModUses(v_env_967_, v_modIdx_968_);
lean_dec(v_modIdx_968_);
lean_dec_ref(v_env_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_970_, lean_object* v_b_971_){
_start:
{
if (lean_obj_tag(v_as_x27_970_) == 0)
{
return v_b_971_;
}
else
{
lean_object* v_head_972_; lean_object* v_tail_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_head_972_ = lean_ctor_get(v_as_x27_970_, 0);
v_tail_973_ = lean_ctor_get(v_as_x27_970_, 1);
v___x_974_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_975_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_976_ = lean_box(1);
v___x_977_ = lean_box(0);
lean_inc_ref(v_b_971_);
v___x_978_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_974_, v___x_975_, v_b_971_, v___x_976_, v___x_977_);
v___x_979_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_978_, v_head_972_);
lean_dec(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v_toEnvExtension_980_; lean_object* v_asyncMode_981_; lean_object* v___x_982_; 
v_toEnvExtension_980_ = lean_ctor_get(v___x_975_, 0);
v_asyncMode_981_ = lean_ctor_get(v_toEnvExtension_980_, 2);
lean_inc(v_head_972_);
v___x_982_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_975_, v_b_971_, v_head_972_, v_asyncMode_981_, v___x_977_);
v_as_x27_970_ = v_tail_973_;
v_b_971_ = v___x_982_;
goto _start;
}
else
{
v_as_x27_970_ = v_tail_973_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_985_, lean_object* v_b_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_985_, v_b_986_);
lean_dec(v_as_x27_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_988_, lean_object* v_dest_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_990_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_991_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_992_ = lean_box(1);
v___x_993_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_990_, v___x_991_, v_src_988_, v___x_992_);
v___x_994_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_993_, v_dest_989_);
lean_dec(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_995_, lean_object* v_as_x27_996_, lean_object* v_b_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_996_, v_b_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_1000_, lean_object* v_as_x27_1001_, lean_object* v_b_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_1000_, v_as_x27_1001_, v_b_1002_, v_a_1003_);
lean_dec(v_as_x27_1001_);
lean_dec(v_as_1000_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1005_, lean_object* v_entry_1006_, lean_object* v___x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v_toEnvExtension_1009_; lean_object* v_asyncMode_1010_; lean_object* v___x_1011_; 
v_toEnvExtension_1009_ = lean_ctor_get(v___x_1005_, 0);
v_asyncMode_1010_ = lean_ctor_get(v_toEnvExtension_1009_, 2);
lean_inc(v_asyncMode_1010_);
v___x_1011_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1005_, v_x_1008_, v_entry_1006_, v_asyncMode_1010_, v___x_1007_);
lean_dec(v_asyncMode_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_modifyEnv_1031_, lean_object* v___f_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_cls_1037_, lean_object* v_toBind_1038_, lean_object* v___f_1039_, lean_object* v_mod_1040_, lean_object* v_hint_1041_, uint8_t v_isMeta_1042_, uint8_t v_isExporting_1043_, uint8_t v_____do__lift_1044_){
_start:
{
lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1052_; lean_object* v___y_1053_; 
if (v_____do__lift_1044_ == 0)
{
lean_object* v___x_1065_; 
lean_dec(v_hint_1041_);
lean_dec(v_mod_1040_);
lean_dec(v___f_1039_);
lean_dec(v_toBind_1038_);
lean_dec(v_cls_1037_);
lean_dec(v_inst_1036_);
lean_dec_ref(v_inst_1035_);
lean_dec_ref(v_inst_1034_);
lean_dec_ref(v_inst_1033_);
v___x_1065_ = lean_apply_1(v_modifyEnv_1031_, v___f_1032_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___y_1068_; 
lean_dec_ref(v___f_1032_);
lean_dec(v_modifyEnv_1031_);
v___x_1066_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
if (v_isExporting_1043_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12));
v___y_1068_ = v___x_1075_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13));
v___y_1068_ = v___x_1076_;
goto v___jp_1067_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_inc_ref(v___y_1068_);
v___x_1069_ = l_Lean_stringToMessageData(v___y_1068_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1066_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
if (v_isMeta_1042_ == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10));
v___y_1052_ = v___x_1072_;
v___y_1053_ = v___x_1073_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11));
v___y_1052_ = v___x_1072_;
v___y_1053_ = v___x_1074_;
goto v___jp_1051_;
}
}
}
v___jp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___y_1046_);
lean_ctor_set(v___x_1048_, 1, v___y_1047_);
v___x_1049_ = l_Lean_addTrace___redArg(v_inst_1033_, v_inst_1034_, v_inst_1035_, v_inst_1036_, v_cls_1037_, v___x_1048_);
v___x_1050_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1049_, v___f_1039_);
return v___x_1050_;
}
v___jp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
lean_inc_ref(v___y_1053_);
v___x_1054_ = l_Lean_stringToMessageData(v___y_1053_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___y_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_MessageData_ofName(v_mod_1040_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_Name_isAnonymous(v_hint_1041_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
v___x_1062_ = l_Lean_MessageData_ofName(v_hint_1041_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___y_1046_ = v___x_1059_;
v___y_1047_ = v___x_1063_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1064_; 
lean_dec(v_hint_1041_);
v___x_1064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
v___y_1046_ = v___x_1059_;
v___y_1047_ = v___x_1064_;
goto v___jp_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_modifyEnv_1077_, lean_object* v___f_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_cls_1083_, lean_object* v_toBind_1084_, lean_object* v___f_1085_, lean_object* v_mod_1086_, lean_object* v_hint_1087_, lean_object* v_isMeta_1088_, lean_object* v_isExporting_1089_, lean_object* v_____do__lift_1090_){
_start:
{
uint8_t v_isMeta_boxed_1091_; uint8_t v_isExporting_boxed_1092_; uint8_t v_____do__lift_963__boxed_1093_; lean_object* v_res_1094_; 
v_isMeta_boxed_1091_ = lean_unbox(v_isMeta_1088_);
v_isExporting_boxed_1092_ = lean_unbox(v_isExporting_1089_);
v_____do__lift_963__boxed_1093_ = lean_unbox(v_____do__lift_1090_);
v_res_1094_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_modifyEnv_1077_, v___f_1078_, v_inst_1079_, v_inst_1080_, v_inst_1081_, v_inst_1082_, v_cls_1083_, v_toBind_1084_, v___f_1085_, v_mod_1086_, v_hint_1087_, v_isMeta_boxed_1091_, v_isExporting_boxed_1092_, v_____do__lift_963__boxed_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v___x_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v_entry_1098_, lean_object* v_inst_1099_, lean_object* v_toApplicative_1100_, lean_object* v_modifyEnv_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_toBind_1105_, lean_object* v_mod_1106_, lean_object* v_hint_1107_, uint8_t v_isMeta_1108_, uint8_t v_isExporting_1109_, lean_object* v_inst_1110_, lean_object* v_____do__lift_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1112_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1113_ = lean_box(1);
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1095_, v___x_1112_, v_____do__lift_1111_, v___x_1113_, v___x_1114_);
lean_inc_ref(v_entry_1098_);
v___x_1116_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1096_, v___x_1097_, v___x_1115_, v_entry_1098_);
if (v___x_1116_ == 0)
{
lean_object* v_getInheritedTraceOptions_1117_; lean_object* v_toPure_1118_; lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v_cls_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_getInheritedTraceOptions_1117_ = lean_ctor_get(v_inst_1099_, 2);
lean_inc(v_getInheritedTraceOptions_1117_);
v_toPure_1118_ = lean_ctor_get(v_toApplicative_1100_, 1);
lean_inc(v_toPure_1118_);
lean_dec_ref(v_toApplicative_1100_);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1119_, 0, v___x_1112_);
lean_closure_set(v___f_1119_, 1, v_entry_1098_);
lean_closure_set(v___f_1119_, 2, v___x_1114_);
lean_inc_ref(v___f_1119_);
lean_inc(v_modifyEnv_1101_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1120_, 0, v_modifyEnv_1101_);
lean_closure_set(v___f_1120_, 1, v___f_1119_);
v_cls_1121_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1122_ = lean_box(v_isMeta_1108_);
v___x_1123_ = lean_box(v_isExporting_1109_);
lean_inc_n(v_toBind_1105_, 3);
v___f_1124_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1124_, 0, v_modifyEnv_1101_);
lean_closure_set(v___f_1124_, 1, v___f_1119_);
lean_closure_set(v___f_1124_, 2, v_inst_1102_);
lean_closure_set(v___f_1124_, 3, v_inst_1099_);
lean_closure_set(v___f_1124_, 4, v_inst_1103_);
lean_closure_set(v___f_1124_, 5, v_inst_1104_);
lean_closure_set(v___f_1124_, 6, v_cls_1121_);
lean_closure_set(v___f_1124_, 7, v_toBind_1105_);
lean_closure_set(v___f_1124_, 8, v___f_1120_);
lean_closure_set(v___f_1124_, 9, v_mod_1106_);
lean_closure_set(v___f_1124_, 10, v_hint_1107_);
lean_closure_set(v___f_1124_, 11, v___x_1122_);
lean_closure_set(v___f_1124_, 12, v___x_1123_);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1125_, 0, v_toPure_1118_);
lean_closure_set(v___f_1125_, 1, v_cls_1121_);
lean_closure_set(v___f_1125_, 2, v_toBind_1105_);
lean_closure_set(v___f_1125_, 3, v_inst_1110_);
v___x_1126_ = lean_apply_4(v_toBind_1105_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1117_, v___f_1125_);
v___x_1127_ = lean_apply_4(v_toBind_1105_, lean_box(0), lean_box(0), v___x_1126_, v___f_1124_);
return v___x_1127_;
}
else
{
lean_object* v_toPure_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v_inst_1110_);
lean_dec(v_hint_1107_);
lean_dec(v_mod_1106_);
lean_dec(v_toBind_1105_);
lean_dec(v_inst_1104_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
lean_dec(v_modifyEnv_1101_);
lean_dec_ref(v_inst_1099_);
lean_dec_ref(v_entry_1098_);
v_toPure_1128_ = lean_ctor_get(v_toApplicative_1100_, 1);
lean_inc(v_toPure_1128_);
lean_dec_ref(v_toApplicative_1100_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_apply_2(v_toPure_1128_, lean_box(0), v___x_1129_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1131_ = _args[0];
lean_object* v___x_1132_ = _args[1];
lean_object* v___x_1133_ = _args[2];
lean_object* v_entry_1134_ = _args[3];
lean_object* v_inst_1135_ = _args[4];
lean_object* v_toApplicative_1136_ = _args[5];
lean_object* v_modifyEnv_1137_ = _args[6];
lean_object* v_inst_1138_ = _args[7];
lean_object* v_inst_1139_ = _args[8];
lean_object* v_inst_1140_ = _args[9];
lean_object* v_toBind_1141_ = _args[10];
lean_object* v_mod_1142_ = _args[11];
lean_object* v_hint_1143_ = _args[12];
lean_object* v_isMeta_1144_ = _args[13];
lean_object* v_isExporting_1145_ = _args[14];
lean_object* v_inst_1146_ = _args[15];
lean_object* v_____do__lift_1147_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1148_; uint8_t v_isExporting_boxed_1149_; lean_object* v_res_1150_; 
v_isMeta_boxed_1148_ = lean_unbox(v_isMeta_1144_);
v_isExporting_boxed_1149_ = lean_unbox(v_isExporting_1145_);
v_res_1150_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v___x_1131_, v___x_1132_, v___x_1133_, v_entry_1134_, v_inst_1135_, v_toApplicative_1136_, v_modifyEnv_1137_, v_inst_1138_, v_inst_1139_, v_inst_1140_, v_toBind_1141_, v_mod_1142_, v_hint_1143_, v_isMeta_boxed_1148_, v_isExporting_boxed_1149_, v_inst_1146_, v_____do__lift_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v_mod_1151_, uint8_t v_isMeta_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v_inst_1156_, lean_object* v_toApplicative_1157_, lean_object* v_modifyEnv_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_toBind_1162_, lean_object* v_hint_1163_, lean_object* v_inst_1164_, lean_object* v_getEnv_1165_, lean_object* v_____do__lift_1166_){
_start:
{
uint8_t v_isExporting_1167_; lean_object* v_entry_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; 
v_isExporting_1167_ = lean_ctor_get_uint8(v_____do__lift_1166_, sizeof(void*)*8);
lean_inc(v_mod_1151_);
v_entry_1168_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1168_, 0, v_mod_1151_);
lean_ctor_set_uint8(v_entry_1168_, sizeof(void*)*1, v_isExporting_1167_);
lean_ctor_set_uint8(v_entry_1168_, sizeof(void*)*1 + 1, v_isMeta_1152_);
v___x_1169_ = lean_box(v_isMeta_1152_);
v___x_1170_ = lean_box(v_isExporting_1167_);
lean_inc(v_toBind_1162_);
v___f_1171_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1171_, 0, v___x_1153_);
lean_closure_set(v___f_1171_, 1, v___x_1154_);
lean_closure_set(v___f_1171_, 2, v___x_1155_);
lean_closure_set(v___f_1171_, 3, v_entry_1168_);
lean_closure_set(v___f_1171_, 4, v_inst_1156_);
lean_closure_set(v___f_1171_, 5, v_toApplicative_1157_);
lean_closure_set(v___f_1171_, 6, v_modifyEnv_1158_);
lean_closure_set(v___f_1171_, 7, v_inst_1159_);
lean_closure_set(v___f_1171_, 8, v_inst_1160_);
lean_closure_set(v___f_1171_, 9, v_inst_1161_);
lean_closure_set(v___f_1171_, 10, v_toBind_1162_);
lean_closure_set(v___f_1171_, 11, v_mod_1151_);
lean_closure_set(v___f_1171_, 12, v_hint_1163_);
lean_closure_set(v___f_1171_, 13, v___x_1169_);
lean_closure_set(v___f_1171_, 14, v___x_1170_);
lean_closure_set(v___f_1171_, 15, v_inst_1164_);
v___x_1172_ = lean_apply_4(v_toBind_1162_, lean_box(0), lean_box(0), v_getEnv_1165_, v___f_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object* v_mod_1173_, lean_object* v_isMeta_1174_, lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v___x_1177_, lean_object* v_inst_1178_, lean_object* v_toApplicative_1179_, lean_object* v_modifyEnv_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_toBind_1184_, lean_object* v_hint_1185_, lean_object* v_inst_1186_, lean_object* v_getEnv_1187_, lean_object* v_____do__lift_1188_){
_start:
{
uint8_t v_isMeta_boxed_1189_; lean_object* v_res_1190_; 
v_isMeta_boxed_1189_ = lean_unbox(v_isMeta_1174_);
v_res_1190_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v_mod_1173_, v_isMeta_boxed_1189_, v___x_1175_, v___x_1176_, v___x_1177_, v_inst_1178_, v_toApplicative_1179_, v_modifyEnv_1180_, v_inst_1181_, v_inst_1182_, v_inst_1183_, v_toBind_1184_, v_hint_1185_, v_inst_1186_, v_getEnv_1187_, v_____do__lift_1188_);
lean_dec_ref(v_____do__lift_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_mod_1197_, uint8_t v_isMeta_1198_, lean_object* v_hint_1199_){
_start:
{
lean_object* v_toApplicative_1200_; lean_object* v_toBind_1201_; lean_object* v_getEnv_1202_; lean_object* v_modifyEnv_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
v_toApplicative_1200_ = lean_ctor_get(v_inst_1191_, 0);
lean_inc_ref(v_toApplicative_1200_);
v_toBind_1201_ = lean_ctor_get(v_inst_1191_, 1);
lean_inc_n(v_toBind_1201_, 2);
v_getEnv_1202_ = lean_ctor_get(v_inst_1192_, 0);
lean_inc_n(v_getEnv_1202_, 2);
v_modifyEnv_1203_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc(v_modifyEnv_1203_);
lean_dec_ref(v_inst_1192_);
v___x_1204_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1205_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1206_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1207_ = lean_box(v_isMeta_1198_);
v___f_1208_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 16, 15);
lean_closure_set(v___f_1208_, 0, v_mod_1197_);
lean_closure_set(v___f_1208_, 1, v___x_1207_);
lean_closure_set(v___f_1208_, 2, v___x_1206_);
lean_closure_set(v___f_1208_, 3, v___x_1204_);
lean_closure_set(v___f_1208_, 4, v___x_1205_);
lean_closure_set(v___f_1208_, 5, v_inst_1193_);
lean_closure_set(v___f_1208_, 6, v_toApplicative_1200_);
lean_closure_set(v___f_1208_, 7, v_modifyEnv_1203_);
lean_closure_set(v___f_1208_, 8, v_inst_1191_);
lean_closure_set(v___f_1208_, 9, v_inst_1195_);
lean_closure_set(v___f_1208_, 10, v_inst_1196_);
lean_closure_set(v___f_1208_, 11, v_toBind_1201_);
lean_closure_set(v___f_1208_, 12, v_hint_1199_);
lean_closure_set(v___f_1208_, 13, v_inst_1194_);
lean_closure_set(v___f_1208_, 14, v_getEnv_1202_);
v___x_1209_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v_getEnv_1202_, v___f_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_mod_1216_, lean_object* v_isMeta_1217_, lean_object* v_hint_1218_){
_start:
{
uint8_t v_isMeta_boxed_1219_; lean_object* v_res_1220_; 
v_isMeta_boxed_1219_ = lean_unbox(v_isMeta_1217_);
v_res_1220_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1210_, v_inst_1211_, v_inst_1212_, v_inst_1213_, v_inst_1214_, v_inst_1215_, v_mod_1216_, v_isMeta_boxed_1219_, v_hint_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_mod_1228_, uint8_t v_isMeta_1229_, lean_object* v_hint_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1222_, v_inst_1223_, v_inst_1224_, v_inst_1225_, v_inst_1226_, v_inst_1227_, v_mod_1228_, v_isMeta_1229_, v_hint_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_mod_1239_, lean_object* v_isMeta_1240_, lean_object* v_hint_1241_){
_start:
{
uint8_t v_isMeta_boxed_1242_; lean_object* v_res_1243_; 
v_isMeta_boxed_1242_ = lean_unbox(v_isMeta_1240_);
v_res_1243_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_inst_1237_, v_inst_1238_, v_mod_1239_, v_isMeta_boxed_1242_, v_hint_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, uint8_t v_isMeta_1251_, lean_object* v_toApplicative_1252_, lean_object* v_____do__lift_1253_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = l_Lean_Environment_mainModule(v_____do__lift_1253_);
v___x_1255_ = lean_name_eq(v_modName_1244_, v___x_1254_);
lean_dec(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v_toApplicative_1252_);
v___x_1256_ = lean_box(0);
v___x_1257_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1245_, v_inst_1246_, v_inst_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_modName_1244_, v_isMeta_1251_, v___x_1256_);
return v___x_1257_;
}
else
{
lean_object* v_toPure_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_inst_1250_);
lean_dec_ref(v_inst_1249_);
lean_dec(v_inst_1248_);
lean_dec_ref(v_inst_1247_);
lean_dec_ref(v_inst_1246_);
lean_dec_ref(v_inst_1245_);
lean_dec(v_modName_1244_);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1252_, 1);
lean_inc(v_toPure_1258_);
lean_dec_ref(v_toApplicative_1252_);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_apply_2(v_toPure_1258_, lean_box(0), v___x_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_isMeta_1268_, lean_object* v_toApplicative_1269_, lean_object* v_____do__lift_1270_){
_start:
{
uint8_t v_isMeta_boxed_1271_; lean_object* v_res_1272_; 
v_isMeta_boxed_1271_ = lean_unbox(v_isMeta_1268_);
v_res_1272_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1261_, v_inst_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_isMeta_boxed_1271_, v_toApplicative_1269_, v_____do__lift_1270_);
lean_dec_ref(v_____do__lift_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_modName_1279_, uint8_t v_isMeta_1280_){
_start:
{
lean_object* v_toApplicative_1281_; lean_object* v_toBind_1282_; lean_object* v_getEnv_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; 
v_toApplicative_1281_ = lean_ctor_get(v_inst_1273_, 0);
lean_inc_ref(v_toApplicative_1281_);
v_toBind_1282_ = lean_ctor_get(v_inst_1273_, 1);
lean_inc(v_toBind_1282_);
v_getEnv_1283_ = lean_ctor_get(v_inst_1274_, 0);
lean_inc(v_getEnv_1283_);
v___x_1284_ = lean_box(v_isMeta_1280_);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1285_, 0, v_modName_1279_);
lean_closure_set(v___f_1285_, 1, v_inst_1273_);
lean_closure_set(v___f_1285_, 2, v_inst_1274_);
lean_closure_set(v___f_1285_, 3, v_inst_1275_);
lean_closure_set(v___f_1285_, 4, v_inst_1276_);
lean_closure_set(v___f_1285_, 5, v_inst_1277_);
lean_closure_set(v___f_1285_, 6, v_inst_1278_);
lean_closure_set(v___f_1285_, 7, v___x_1284_);
lean_closure_set(v___f_1285_, 8, v_toApplicative_1281_);
v___x_1286_ = lean_apply_4(v_toBind_1282_, lean_box(0), lean_box(0), v_getEnv_1283_, v___f_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_modName_1293_, lean_object* v_isMeta_1294_){
_start:
{
uint8_t v_isMeta_boxed_1295_; lean_object* v_res_1296_; 
v_isMeta_boxed_1295_ = lean_unbox(v_isMeta_1294_);
v_res_1296_ = l_Lean_recordExtraModUse___redArg(v_inst_1287_, v_inst_1288_, v_inst_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v_modName_1293_, v_isMeta_boxed_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_modName_1304_, uint8_t v_isMeta_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_recordExtraModUse___redArg(v_inst_1298_, v_inst_1299_, v_inst_1300_, v_inst_1301_, v_inst_1302_, v_inst_1303_, v_modName_1304_, v_isMeta_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_modName_1314_, lean_object* v_isMeta_1315_){
_start:
{
uint8_t v_isMeta_boxed_1316_; lean_object* v_res_1317_; 
v_isMeta_boxed_1316_ = lean_unbox(v_isMeta_1315_);
v_res_1317_ = l_Lean_recordExtraModUse(v_m_1307_, v_inst_1308_, v_inst_1309_, v_inst_1310_, v_inst_1311_, v_inst_1312_, v_inst_1313_, v_modName_1314_, v_isMeta_boxed_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1318_, lean_object* v_____s_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_apply_2(v_toPure_1318_, lean_box(0), v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1322_, lean_object* v_toPure_1323_, lean_object* v_r_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1322_);
v___x_1326_ = lean_apply_2(v_toPure_1323_, lean_box(0), v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1327_, lean_object* v___x_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_declName_1335_, lean_object* v_toBind_1336_, lean_object* v___f_1337_, lean_object* v_a_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v_modules_1342_; lean_object* v___x_1343_; lean_object* v_toImport_1344_; lean_object* v_module_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1341_ = l_Lean_Environment_header(v_env_1327_);
v_modules_1342_ = lean_ctor_get(v___x_1341_, 3);
lean_inc_ref(v_modules_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_array_get(v___x_1328_, v_modules_1342_, v_a_1338_);
lean_dec_ref(v_modules_1342_);
v_toImport_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_ref(v_toImport_1344_);
lean_dec(v___x_1343_);
v_module_1345_ = lean_ctor_get(v_toImport_1344_, 0);
lean_inc(v_module_1345_);
lean_dec_ref(v_toImport_1344_);
v___x_1346_ = 0;
v___x_1347_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_inst_1333_, v_inst_1334_, v_module_1345_, v___x_1346_, v_declName_1335_);
v___x_1348_ = lean_apply_4(v_toBind_1336_, lean_box(0), lean_box(0), v___x_1347_, v___f_1337_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1349_, lean_object* v___x_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_declName_1357_, lean_object* v_toBind_1358_, lean_object* v___f_1359_, lean_object* v_a_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1349_, v___x_1350_, v_inst_1351_, v_inst_1352_, v_inst_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_declName_1357_, v_toBind_1358_, v___f_1359_, v_a_1360_, v_x_1361_, v___y_1362_);
lean_dec(v_a_1360_);
lean_dec_ref(v___x_1350_);
lean_dec_ref(v_env_1349_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1364_, lean_object* v_env_1365_, lean_object* v___x_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_inst_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_declName_1373_, lean_object* v_toBind_1374_, lean_object* v___f_1375_, lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v_____r_1379_){
_start:
{
lean_object* v___y_1381_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1389_ = l_Lean_indirectModUseExt;
v___x_1390_ = lean_box(1);
v___x_1391_ = lean_box(0);
lean_inc_ref(v_env_1365_);
v___x_1392_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1376_, v___x_1389_, v_env_1365_, v___x_1390_, v___x_1391_);
lean_inc(v_declName_1373_);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1377_, v___x_1378_, v___x_1392_, v_declName_1373_);
lean_dec(v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1381_ = v___x_1394_;
goto v___jp_1380_;
}
else
{
lean_object* v_val_1395_; 
v_val_1395_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___x_1393_, 1);
v___y_1381_ = v_val_1395_;
goto v___jp_1380_;
}
v___jp_1380_:
{
lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; size_t v_sz_1385_; size_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1382_ = lean_box(0);
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1383_, 0, v___x_1382_);
lean_closure_set(v___f_1383_, 1, v_toPure_1364_);
lean_inc(v_toBind_1374_);
lean_inc_ref(v_inst_1367_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1384_, 0, v_env_1365_);
lean_closure_set(v___f_1384_, 1, v___x_1366_);
lean_closure_set(v___f_1384_, 2, v_inst_1367_);
lean_closure_set(v___f_1384_, 3, v_inst_1368_);
lean_closure_set(v___f_1384_, 4, v_inst_1369_);
lean_closure_set(v___f_1384_, 5, v_inst_1370_);
lean_closure_set(v___f_1384_, 6, v_inst_1371_);
lean_closure_set(v___f_1384_, 7, v_inst_1372_);
lean_closure_set(v___f_1384_, 8, v_declName_1373_);
lean_closure_set(v___f_1384_, 9, v_toBind_1374_);
lean_closure_set(v___f_1384_, 10, v___f_1383_);
v_sz_1385_ = lean_array_size(v___y_1381_);
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1367_, v___y_1381_, v___f_1384_, v_sz_1385_, v___x_1386_, v___x_1382_);
v___x_1388_ = lean_apply_4(v_toBind_1374_, lean_box(0), lean_box(0), v___x_1387_, v___f_1375_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_declName_1403_, lean_object* v_toBind_1404_, lean_object* v___f_1405_, uint8_t v_isMeta_1406_, lean_object* v_____do__lift_1407_){
_start:
{
uint8_t v___y_1409_; 
if (v_isMeta_1406_ == 0)
{
lean_dec_ref(v_____do__lift_1407_);
v___y_1409_ = v_isMeta_1406_;
goto v___jp_1408_;
}
else
{
uint8_t v___x_1414_; 
lean_inc(v_declName_1403_);
v___x_1414_ = l_Lean_isMarkedMeta(v_____do__lift_1407_, v_declName_1403_);
if (v___x_1414_ == 0)
{
v___y_1409_ = v_isMeta_1406_;
goto v___jp_1408_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = 0;
v___y_1409_ = v___x_1415_;
goto v___jp_1408_;
}
}
v___jp_1408_:
{
lean_object* v_toImport_1410_; lean_object* v_module_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_toImport_1410_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_toImport_1410_);
lean_dec_ref(v___x_1396_);
v_module_1411_ = lean_ctor_get(v_toImport_1410_, 0);
lean_inc(v_module_1411_);
lean_dec_ref(v_toImport_1410_);
v___x_1412_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1397_, v_inst_1398_, v_inst_1399_, v_inst_1400_, v_inst_1401_, v_inst_1402_, v_module_1411_, v___y_1409_, v_declName_1403_);
v___x_1413_ = lean_apply_4(v_toBind_1404_, lean_box(0), lean_box(0), v___x_1412_, v___f_1405_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_declName_1423_, lean_object* v_toBind_1424_, lean_object* v___f_1425_, lean_object* v_isMeta_1426_, lean_object* v_____do__lift_1427_){
_start:
{
uint8_t v_isMeta_boxed_1428_; lean_object* v_res_1429_; 
v_isMeta_boxed_1428_ = lean_unbox(v_isMeta_1426_);
v_res_1429_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1416_, v_inst_1417_, v_inst_1418_, v_inst_1419_, v_inst_1420_, v_inst_1421_, v_inst_1422_, v_declName_1423_, v_toBind_1424_, v___f_1425_, v_isMeta_boxed_1428_, v_____do__lift_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1430_, lean_object* v_declName_1431_, lean_object* v___x_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_toBind_1439_, lean_object* v___f_1440_, lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, uint8_t v_isMeta_1444_, lean_object* v_getEnv_1445_, lean_object* v_env_1446_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1446_, v_declName_1431_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref(v_env_1446_);
lean_dec(v_getEnv_1445_);
lean_dec_ref(v___x_1443_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v___x_1441_);
lean_dec(v___f_1440_);
lean_dec(v_toBind_1439_);
lean_dec(v_inst_1438_);
lean_dec_ref(v_inst_1437_);
lean_dec(v_inst_1436_);
lean_dec_ref(v_inst_1435_);
lean_dec_ref(v_inst_1434_);
lean_dec_ref(v_inst_1433_);
lean_dec_ref(v___x_1432_);
lean_dec(v_declName_1431_);
goto v___jp_1447_;
}
else
{
lean_object* v_val_1451_; lean_object* v___x_1452_; lean_object* v_modules_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_val_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = l_Lean_Environment_header(v_env_1446_);
v_modules_1453_ = lean_ctor_get(v___x_1452_, 3);
lean_inc_ref(v_modules_1453_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = lean_array_get_size(v_modules_1453_);
v___x_1455_ = lean_nat_dec_lt(v_val_1451_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec_ref(v_modules_1453_);
lean_dec(v_val_1451_);
lean_dec_ref(v_env_1446_);
lean_dec(v_getEnv_1445_);
lean_dec_ref(v___x_1443_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v___x_1441_);
lean_dec(v___f_1440_);
lean_dec(v_toBind_1439_);
lean_dec(v_inst_1438_);
lean_dec_ref(v_inst_1437_);
lean_dec(v_inst_1436_);
lean_dec_ref(v_inst_1435_);
lean_dec_ref(v_inst_1434_);
lean_dec_ref(v_inst_1433_);
lean_dec_ref(v___x_1432_);
lean_dec(v_declName_1431_);
goto v___jp_1447_;
}
else
{
lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; 
lean_inc_n(v_toBind_1439_, 2);
lean_inc(v_declName_1431_);
lean_inc(v_inst_1438_);
lean_inc_ref(v_inst_1437_);
lean_inc(v_inst_1436_);
lean_inc_ref(v_inst_1435_);
lean_inc_ref(v_inst_1434_);
lean_inc_ref(v_inst_1433_);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1456_, 0, v_toPure_1430_);
lean_closure_set(v___f_1456_, 1, v_env_1446_);
lean_closure_set(v___f_1456_, 2, v___x_1432_);
lean_closure_set(v___f_1456_, 3, v_inst_1433_);
lean_closure_set(v___f_1456_, 4, v_inst_1434_);
lean_closure_set(v___f_1456_, 5, v_inst_1435_);
lean_closure_set(v___f_1456_, 6, v_inst_1436_);
lean_closure_set(v___f_1456_, 7, v_inst_1437_);
lean_closure_set(v___f_1456_, 8, v_inst_1438_);
lean_closure_set(v___f_1456_, 9, v_declName_1431_);
lean_closure_set(v___f_1456_, 10, v_toBind_1439_);
lean_closure_set(v___f_1456_, 11, v___f_1440_);
lean_closure_set(v___f_1456_, 12, v___x_1441_);
lean_closure_set(v___f_1456_, 13, v___x_1442_);
lean_closure_set(v___f_1456_, 14, v___x_1443_);
v___x_1457_ = lean_array_fget(v_modules_1453_, v_val_1451_);
lean_dec(v_val_1451_);
lean_dec_ref(v_modules_1453_);
v___x_1458_ = lean_box(v_isMeta_1444_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1459_, 0, v___x_1457_);
lean_closure_set(v___f_1459_, 1, v_inst_1433_);
lean_closure_set(v___f_1459_, 2, v_inst_1434_);
lean_closure_set(v___f_1459_, 3, v_inst_1435_);
lean_closure_set(v___f_1459_, 4, v_inst_1436_);
lean_closure_set(v___f_1459_, 5, v_inst_1437_);
lean_closure_set(v___f_1459_, 6, v_inst_1438_);
lean_closure_set(v___f_1459_, 7, v_declName_1431_);
lean_closure_set(v___f_1459_, 8, v_toBind_1439_);
lean_closure_set(v___f_1459_, 9, v___f_1456_);
lean_closure_set(v___f_1459_, 10, v___x_1458_);
v___x_1460_ = lean_apply_4(v_toBind_1439_, lean_box(0), lean_box(0), v_getEnv_1445_, v___f_1459_);
return v___x_1460_;
}
}
v___jp_1447_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_apply_2(v_toPure_1430_, lean_box(0), v___x_1448_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1461_ = _args[0];
lean_object* v_declName_1462_ = _args[1];
lean_object* v___x_1463_ = _args[2];
lean_object* v_inst_1464_ = _args[3];
lean_object* v_inst_1465_ = _args[4];
lean_object* v_inst_1466_ = _args[5];
lean_object* v_inst_1467_ = _args[6];
lean_object* v_inst_1468_ = _args[7];
lean_object* v_inst_1469_ = _args[8];
lean_object* v_toBind_1470_ = _args[9];
lean_object* v___f_1471_ = _args[10];
lean_object* v___x_1472_ = _args[11];
lean_object* v___x_1473_ = _args[12];
lean_object* v___x_1474_ = _args[13];
lean_object* v_isMeta_1475_ = _args[14];
lean_object* v_getEnv_1476_ = _args[15];
lean_object* v_env_1477_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1478_; lean_object* v_res_1479_; 
v_isMeta_boxed_1478_ = lean_unbox(v_isMeta_1475_);
v_res_1479_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1461_, v_declName_1462_, v___x_1463_, v_inst_1464_, v_inst_1465_, v_inst_1466_, v_inst_1467_, v_inst_1468_, v_inst_1469_, v_toBind_1470_, v___f_1471_, v___x_1472_, v___x_1473_, v___x_1474_, v_isMeta_boxed_1478_, v_getEnv_1476_, v_env_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_declName_1486_, uint8_t v_isMeta_1487_){
_start:
{
lean_object* v_toApplicative_1488_; lean_object* v_toBind_1489_; lean_object* v_getEnv_1490_; lean_object* v_toPure_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; 
v_toApplicative_1488_ = lean_ctor_get(v_inst_1480_, 0);
v_toBind_1489_ = lean_ctor_get(v_inst_1480_, 1);
lean_inc_n(v_toBind_1489_, 2);
v_getEnv_1490_ = lean_ctor_get(v_inst_1481_, 0);
lean_inc_n(v_getEnv_1490_, 2);
v_toPure_1491_ = lean_ctor_get(v_toApplicative_1488_, 1);
lean_inc_n(v_toPure_1491_, 2);
v___x_1492_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1493_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1494_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1495_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1496_, 0, v_toPure_1491_);
v___x_1497_ = lean_box(v_isMeta_1487_);
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1498_, 0, v_toPure_1491_);
lean_closure_set(v___f_1498_, 1, v_declName_1486_);
lean_closure_set(v___f_1498_, 2, v___x_1495_);
lean_closure_set(v___f_1498_, 3, v_inst_1480_);
lean_closure_set(v___f_1498_, 4, v_inst_1481_);
lean_closure_set(v___f_1498_, 5, v_inst_1482_);
lean_closure_set(v___f_1498_, 6, v_inst_1483_);
lean_closure_set(v___f_1498_, 7, v_inst_1484_);
lean_closure_set(v___f_1498_, 8, v_inst_1485_);
lean_closure_set(v___f_1498_, 9, v_toBind_1489_);
lean_closure_set(v___f_1498_, 10, v___f_1496_);
lean_closure_set(v___f_1498_, 11, v___x_1494_);
lean_closure_set(v___f_1498_, 12, v___x_1492_);
lean_closure_set(v___f_1498_, 13, v___x_1493_);
lean_closure_set(v___f_1498_, 14, v___x_1497_);
lean_closure_set(v___f_1498_, 15, v_getEnv_1490_);
v___x_1499_ = lean_apply_4(v_toBind_1489_, lean_box(0), lean_box(0), v_getEnv_1490_, v___f_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_declName_1506_, lean_object* v_isMeta_1507_){
_start:
{
uint8_t v_isMeta_boxed_1508_; lean_object* v_res_1509_; 
v_isMeta_boxed_1508_ = lean_unbox(v_isMeta_1507_);
v_res_1509_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_declName_1506_, v_isMeta_boxed_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_declName_1517_, uint8_t v_isMeta_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1511_, v_inst_1512_, v_inst_1513_, v_inst_1514_, v_inst_1515_, v_inst_1516_, v_declName_1517_, v_isMeta_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_declName_1527_, lean_object* v_isMeta_1528_){
_start:
{
uint8_t v_isMeta_boxed_1529_; lean_object* v_res_1530_; 
v_isMeta_boxed_1529_ = lean_unbox(v_isMeta_1528_);
v_res_1530_ = l_Lean_recordExtraModUseFromDecl(v_m_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_declName_1527_, v_isMeta_boxed_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1531_, lean_object* v_e_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_box(0);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1536_);
lean_dec_ref(v_x_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_array_mk(v_es_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1556_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1558_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1562_, lean_object* v_modIdx_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1564_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1565_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1566_ = 0;
v___x_1567_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1564_, v___x_1565_, v_env_1562_, v_modIdx_1563_, v___x_1566_);
v___x_1568_ = lean_array_get_size(v___x_1567_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_nat_dec_eq(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = 1;
return v___x_1571_;
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = 0;
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1573_, lean_object* v_modIdx_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Lean_isExtraRevModUse(v_env_1573_, v_modIdx_1574_);
lean_dec(v_modIdx_1574_);
lean_dec_ref(v_env_1573_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_toEnvExtension_1579_; lean_object* v_asyncMode_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_toEnvExtension_1579_ = lean_ctor_get(v___x_1577_, 0);
v_asyncMode_1580_ = lean_ctor_get(v_toEnvExtension_1579_, 2);
lean_inc(v_asyncMode_1580_);
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_box(0);
v___x_1583_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1577_, v_x_1578_, v___x_1581_, v_asyncMode_1580_, v___x_1582_);
lean_dec(v_asyncMode_1580_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(lean_object* v_modifyEnv_1587_, lean_object* v___f_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_cls_1593_, lean_object* v_toBind_1594_, lean_object* v___f_1595_, uint8_t v_____do__lift_1596_){
_start:
{
if (v_____do__lift_1596_ == 0)
{
lean_object* v___x_1597_; 
lean_dec(v___f_1595_);
lean_dec(v_toBind_1594_);
lean_dec(v_cls_1593_);
lean_dec(v_inst_1592_);
lean_dec_ref(v_inst_1591_);
lean_dec_ref(v_inst_1590_);
lean_dec_ref(v_inst_1589_);
v___x_1597_ = lean_apply_1(v_modifyEnv_1587_, v___f_1588_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v___f_1588_);
lean_dec(v_modifyEnv_1587_);
v___x_1598_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1);
v___x_1599_ = l_Lean_addTrace___redArg(v_inst_1589_, v_inst_1590_, v_inst_1591_, v_inst_1592_, v_cls_1593_, v___x_1598_);
v___x_1600_ = lean_apply_4(v_toBind_1594_, lean_box(0), lean_box(0), v___x_1599_, v___f_1595_);
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(lean_object* v_modifyEnv_1601_, lean_object* v___f_1602_, lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_cls_1607_, lean_object* v_toBind_1608_, lean_object* v___f_1609_, lean_object* v_____do__lift_1610_){
_start:
{
uint8_t v_____do__lift_328__boxed_1611_; lean_object* v_res_1612_; 
v_____do__lift_328__boxed_1611_ = lean_unbox(v_____do__lift_1610_);
v_res_1612_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(v_modifyEnv_1601_, v___f_1602_, v_inst_1603_, v_inst_1604_, v_inst_1605_, v_inst_1606_, v_cls_1607_, v_toBind_1608_, v___f_1609_, v_____do__lift_328__boxed_1611_);
return v_res_1612_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___f_1614_; 
v___x_1613_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1614_, 0, v___x_1613_);
return v___f_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v___x_1615_, lean_object* v_toApplicative_1616_, lean_object* v_inst_1617_, lean_object* v_modifyEnv_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_toBind_1622_, lean_object* v_inst_1623_, lean_object* v_____do__lift_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1625_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1626_ = lean_box(1);
v___x_1627_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1615_, v___x_1625_, v_____do__lift_1624_, v___x_1626_);
v___x_1628_ = l_List_isEmpty___redArg(v___x_1627_);
lean_dec(v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v_toPure_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v_inst_1623_);
lean_dec(v_toBind_1622_);
lean_dec(v_inst_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec_ref(v_inst_1619_);
lean_dec(v_modifyEnv_1618_);
lean_dec_ref(v_inst_1617_);
v_toPure_1629_ = lean_ctor_get(v_toApplicative_1616_, 1);
lean_inc(v_toPure_1629_);
lean_dec_ref(v_toApplicative_1616_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_apply_2(v_toPure_1629_, lean_box(0), v___x_1630_);
return v___x_1631_;
}
else
{
lean_object* v_getInheritedTraceOptions_1632_; lean_object* v_toPure_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v_cls_1636_; lean_object* v___f_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_getInheritedTraceOptions_1632_ = lean_ctor_get(v_inst_1617_, 2);
lean_inc(v_getInheritedTraceOptions_1632_);
v_toPure_1633_ = lean_ctor_get(v_toApplicative_1616_, 1);
lean_inc(v_toPure_1633_);
lean_dec_ref(v_toApplicative_1616_);
v___f_1634_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0);
lean_inc(v_modifyEnv_1618_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1635_, 0, v_modifyEnv_1618_);
lean_closure_set(v___f_1635_, 1, v___f_1634_);
v_cls_1636_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1622_, 3);
v___f_1637_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1637_, 0, v_modifyEnv_1618_);
lean_closure_set(v___f_1637_, 1, v___f_1634_);
lean_closure_set(v___f_1637_, 2, v_inst_1619_);
lean_closure_set(v___f_1637_, 3, v_inst_1617_);
lean_closure_set(v___f_1637_, 4, v_inst_1620_);
lean_closure_set(v___f_1637_, 5, v_inst_1621_);
lean_closure_set(v___f_1637_, 6, v_cls_1636_);
lean_closure_set(v___f_1637_, 7, v_toBind_1622_);
lean_closure_set(v___f_1637_, 8, v___f_1635_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1638_, 0, v_toPure_1633_);
lean_closure_set(v___f_1638_, 1, v_cls_1636_);
lean_closure_set(v___f_1638_, 2, v_toBind_1622_);
lean_closure_set(v___f_1638_, 3, v_inst_1623_);
v___x_1639_ = lean_apply_4(v_toBind_1622_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1632_, v___f_1638_);
v___x_1640_ = lean_apply_4(v_toBind_1622_, lean_box(0), lean_box(0), v___x_1639_, v___f_1637_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_){
_start:
{
lean_object* v_toApplicative_1647_; lean_object* v_toBind_1648_; lean_object* v_getEnv_1649_; lean_object* v_modifyEnv_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; 
v_toApplicative_1647_ = lean_ctor_get(v_inst_1641_, 0);
lean_inc_ref(v_toApplicative_1647_);
v_toBind_1648_ = lean_ctor_get(v_inst_1641_, 1);
lean_inc_n(v_toBind_1648_, 2);
v_getEnv_1649_ = lean_ctor_get(v_inst_1642_, 0);
lean_inc(v_getEnv_1649_);
v_modifyEnv_1650_ = lean_ctor_get(v_inst_1642_, 1);
lean_inc(v_modifyEnv_1650_);
lean_dec_ref(v_inst_1642_);
v___x_1651_ = lean_box(0);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4), 10, 9);
lean_closure_set(v___f_1652_, 0, v___x_1651_);
lean_closure_set(v___f_1652_, 1, v_toApplicative_1647_);
lean_closure_set(v___f_1652_, 2, v_inst_1643_);
lean_closure_set(v___f_1652_, 3, v_modifyEnv_1650_);
lean_closure_set(v___f_1652_, 4, v_inst_1641_);
lean_closure_set(v___f_1652_, 5, v_inst_1645_);
lean_closure_set(v___f_1652_, 6, v_inst_1646_);
lean_closure_set(v___f_1652_, 7, v_toBind_1648_);
lean_closure_set(v___f_1652_, 8, v_inst_1644_);
v___x_1653_ = lean_apply_4(v_toBind_1648_, lean_box(0), lean_box(0), v_getEnv_1649_, v___f_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1655_, v_inst_1656_, v_inst_1657_, v_inst_1658_, v_inst_1659_, v_inst_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(4259277863u);
v___x_1677_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1678_ = l_Lean_Name_num___override(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1681_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1682_ = l_Lean_Name_str___override(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1685_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1686_ = l_Lean_Name_str___override(v___x_1685_, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(2u);
v___x_1688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1689_ = l_Lean_Name_num___override(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1691_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1692_ = 0;
v___x_1693_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1694_ = l_Lean_registerTraceClass(v___x_1691_, v___x_1692_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1696_;
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
