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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "recording indirect mod use of `"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__1;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "` ("};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__3;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__4 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "recording extra reverse use of current module"};
static const lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_nbuckets_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_66_ = lean_array_get_size(v_data_65_);
v___x_67_ = lean_unsigned_to_nat(2u);
v_nbuckets_68_ = lean_nat_mul(v___x_66_, v___x_67_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_box(0);
v___x_71_ = lean_mk_array(v_nbuckets_68_, v___x_70_);
v___x_72_ = lean_array_propagate_mark(v_data_65_, v___x_71_);
v___x_73_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_69_, v_data_65_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object* v_val_76_, lean_object* v_x_77_){
_start:
{
lean_object* v___y_79_; 
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_79_ = v___x_82_;
goto v___jp_78_;
}
else
{
lean_object* v_val_83_; 
v_val_83_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v_x_77_, 1);
v___y_79_ = v_val_83_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_array_push(v___y_79_, v_val_76_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_val_84_, lean_object* v_a_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_val_89_; lean_object* v___x_90_; 
v___x_87_ = lean_box(0);
v___x_88_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_84_, v___x_87_);
v_val_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_val_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_90_, 0, v_a_85_);
lean_ctor_set(v___x_90_, 1, v_val_89_);
lean_ctor_set(v___x_90_, 2, v_x_86_);
return v___x_90_;
}
else
{
lean_object* v_key_91_; lean_object* v_value_92_; lean_object* v_tail_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_108_; 
v_key_91_ = lean_ctor_get(v_x_86_, 0);
v_value_92_ = lean_ctor_get(v_x_86_, 1);
v_tail_93_ = lean_ctor_get(v_x_86_, 2);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_108_ == 0)
{
v___x_95_ = v_x_86_;
v_isShared_96_ = v_isSharedCheck_108_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_tail_93_);
lean_inc(v_value_92_);
lean_inc(v_key_91_);
lean_dec(v_x_86_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_108_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v___x_97_; 
v___x_97_ = lean_name_eq(v_key_91_, v_a_85_);
if (v___x_97_ == 0)
{
lean_object* v_tail_98_; lean_object* v___x_100_; 
v_tail_98_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_84_, v_a_85_, v_tail_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 2, v_tail_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_key_91_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_value_92_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_tail_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_val_104_; lean_object* v___x_106_; 
lean_dec(v_key_91_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_value_92_);
v___x_103_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_84_, v___x_102_);
v_val_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_104_);
lean_dec(v___x_103_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v_val_104_);
lean_ctor_set(v___x_95_, 0, v_a_85_);
v___x_106_ = v___x_95_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_85_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_val_104_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_tail_93_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
else
{
lean_object* v_key_112_; lean_object* v_tail_113_; uint8_t v___x_114_; 
v_key_112_ = lean_ctor_get(v_x_110_, 0);
v_tail_113_ = lean_ctor_get(v_x_110_, 2);
v___x_114_ = lean_name_eq(v_key_112_, v_a_109_);
if (v___x_114_ == 0)
{
v_x_110_ = v_tail_113_;
goto _start;
}
else
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v_a_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_val_120_, lean_object* v_m_121_, lean_object* v_a_122_){
_start:
{
size_t v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v_size_130_; lean_object* v_buckets_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_178_; 
v_size_130_ = lean_ctor_get(v_m_121_, 0);
v_buckets_131_ = lean_ctor_get(v_m_121_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_m_121_);
if (v_isSharedCheck_178_ == 0)
{
v___x_133_ = v_m_121_;
v_isShared_134_ = v_isSharedCheck_178_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_buckets_131_);
lean_inc(v_size_130_);
lean_dec(v_m_121_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_178_;
goto v_resetjp_132_;
}
v___jp_123_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_array_uset(v___y_125_, v___y_124_, v___y_126_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___y_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
return v___x_129_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; uint64_t v___y_137_; 
v___x_135_ = lean_array_get_size(v_buckets_131_);
if (lean_obj_tag(v_a_122_) == 0)
{
uint64_t v___x_176_; 
v___x_176_ = 1723ULL;
v___y_137_ = v___x_176_;
goto v___jp_136_;
}
else
{
uint64_t v_hash_177_; 
v_hash_177_ = lean_ctor_get_uint64(v_a_122_, sizeof(void*)*2);
v___y_137_ = v_hash_177_;
goto v___jp_136_;
}
v___jp_136_:
{
uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v_bkt_149_; uint8_t v___x_150_; 
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___y_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___y_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_135_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v_bkt_149_ = lean_array_uget_borrowed(v_buckets_131_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_122_, v_bkt_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_size_x27_154_; lean_object* v___x_155_; lean_object* v_buckets_x27_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_151_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___x_152_ = lean_array_push(v___x_151_, v_val_120_);
v___x_153_ = lean_unsigned_to_nat(1u);
v_size_x27_154_ = lean_nat_add(v_size_130_, v___x_153_);
lean_dec(v_size_130_);
lean_inc(v_bkt_149_);
v___x_155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_155_, 0, v_a_122_);
lean_ctor_set(v___x_155_, 1, v___x_152_);
lean_ctor_set(v___x_155_, 2, v_bkt_149_);
v_buckets_x27_156_ = lean_array_uset(v_buckets_131_, v___x_148_, v___x_155_);
v___x_157_ = lean_unsigned_to_nat(4u);
v___x_158_ = lean_nat_mul(v_size_x27_154_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(3u);
v___x_160_ = lean_nat_div(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_array_get_size(v_buckets_x27_156_);
v___x_162_ = lean_nat_dec_le(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
if (v___x_162_ == 0)
{
lean_object* v_val_163_; lean_object* v___x_165_; 
v_val_163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_156_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_val_163_);
lean_ctor_set(v___x_133_, 0, v_size_x27_154_);
v___x_165_ = v___x_133_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_size_x27_154_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_val_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
else
{
lean_object* v___x_168_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_buckets_x27_156_);
lean_ctor_set(v___x_133_, 0, v_size_x27_154_);
v___x_168_ = v___x_133_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_size_x27_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_buckets_x27_156_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v___x_170_; lean_object* v_buckets_x27_171_; lean_object* v_bkt_x27_172_; uint8_t v___x_173_; 
lean_inc(v_bkt_149_);
lean_del_object(v___x_133_);
v___x_170_ = lean_box(0);
v_buckets_x27_171_ = lean_array_uset(v_buckets_131_, v___x_148_, v___x_170_);
lean_inc(v_a_122_);
v_bkt_x27_172_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_120_, v_a_122_, v_bkt_149_);
v___x_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_122_, v_bkt_x27_172_);
lean_dec(v_a_122_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_sub(v_size_130_, v___x_174_);
lean_dec(v_size_130_);
v___y_124_ = v___x_148_;
v___y_125_ = v_buckets_x27_171_;
v___y_126_ = v_bkt_x27_172_;
v___y_127_ = v___x_175_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_148_;
v___y_125_ = v_buckets_x27_171_;
v___y_126_ = v_bkt_x27_172_;
v___y_127_ = v_size_130_;
goto v___jp_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_val_179_, lean_object* v_as_180_, size_t v_sz_181_, size_t v_i_182_, lean_object* v_b_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = lean_usize_dec_lt(v_i_182_, v_sz_181_);
if (v___x_184_ == 0)
{
lean_dec(v_val_179_);
return v_b_183_;
}
else
{
lean_object* v_a_185_; lean_object* v_declName_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; 
v_a_185_ = lean_array_uget_borrowed(v_as_180_, v_i_182_);
v_declName_186_ = lean_ctor_get(v_a_185_, 1);
lean_inc(v_declName_186_);
lean_inc(v_val_179_);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_179_, v_b_183_, v_declName_186_);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_182_, v___x_188_);
v_i_182_ = v___x_189_;
v_b_183_ = v___x_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_val_191_, lean_object* v_as_192_, lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_b_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_191_, v_as_192_, v_sz_boxed_196_, v_i_boxed_197_, v_b_195_);
lean_dec_ref(v_as_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_as_199_, size_t v_sz_200_, size_t v_i_201_, lean_object* v_b_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_usize_dec_lt(v_i_201_, v_sz_200_);
if (v___x_203_ == 0)
{
return v_b_202_;
}
else
{
lean_object* v_snd_204_; 
v_snd_204_ = lean_ctor_get(v_b_202_, 1);
lean_inc(v_snd_204_);
if (lean_obj_tag(v_snd_204_) == 0)
{
lean_object* v_fst_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_fst_205_ = lean_ctor_get(v_b_202_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_b_202_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_b_202_, 1);
lean_dec(v_unused_213_);
v___x_207_ = v_b_202_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_fst_205_);
lean_dec(v_b_202_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_fst_205_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_snd_204_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_fst_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_238_; 
v_fst_214_ = lean_ctor_get(v_b_202_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_b_202_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_b_202_, 1);
lean_dec(v_unused_239_);
v___x_216_ = v_b_202_;
v_isShared_217_ = v_isSharedCheck_238_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_fst_214_);
lean_dec(v_b_202_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_238_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_237_; 
v_val_218_ = lean_ctor_get(v_snd_204_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_snd_204_);
if (v_isSharedCheck_237_ == 0)
{
v___x_220_ = v_snd_204_;
v_isShared_221_ = v_isSharedCheck_237_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v_snd_204_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_237_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v_a_222_ = lean_array_uget_borrowed(v_as_199_, v_i_201_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_val_218_, v___x_223_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_224_);
v___x_226_ = v___x_220_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_236_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
size_t v_sz_227_; size_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v_sz_227_ = lean_array_size(v_a_222_);
v___x_228_ = ((size_t)0ULL);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_218_, v_a_222_, v_sz_227_, v___x_228_, v_fst_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_226_);
lean_ctor_set(v___x_216_, 0, v___x_229_);
v___x_231_ = v___x_216_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_226_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
size_t v___x_232_; size_t v___x_233_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_201_, v___x_232_);
v_i_201_ = v___x_233_;
v_b_202_ = v___x_231_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_240_, lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_b_243_){
_start:
{
size_t v_sz_boxed_244_; size_t v_i_boxed_245_; lean_object* v_res_246_; 
v_sz_boxed_244_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_240_, v_sz_boxed_244_, v_i_boxed_245_, v_b_243_);
lean_dec_ref(v_as_240_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_unsigned_to_nat(16u);
v___x_249_ = lean_mk_array(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_s_252_; 
v___x_250_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_251_ = lean_unsigned_to_nat(0u);
v_s_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_252_, 0, v___x_251_);
lean_ctor_set(v_s_252_, 1, v___x_250_);
return v_s_252_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_255_; lean_object* v_s_256_; lean_object* v___x_257_; 
v___x_255_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_256_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_s_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_258_){
_start:
{
lean_object* v___x_259_; size_t v_sz_260_; size_t v___x_261_; lean_object* v___x_262_; lean_object* v_fst_263_; 
v___x_259_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_260_ = lean_array_size(v_es_258_);
v___x_261_ = ((size_t)0ULL);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_258_, v_sz_260_, v___x_261_, v___x_259_);
v_fst_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_fst_263_);
lean_dec_ref(v___x_262_);
return v_fst_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_264_);
lean_dec_ref(v_es_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_283_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_286_, lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_287_, v_x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_290_, lean_object* v_a_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_290_, v_a_291_, v_x_292_);
lean_dec(v_x_292_);
lean_dec(v_a_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_295_, lean_object* v_data_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_298_, lean_object* v_i_299_, lean_object* v_source_300_, lean_object* v_target_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_299_, v_source_300_, v_target_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_304_, v_x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__2(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_310_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_311_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object* v_env_315_, lean_object* v_modIdx_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__3, &l_Lean_getIndirectModUses___closed__3_once, _init_l_Lean_getIndirectModUses___closed__3);
v___x_318_ = l_Lean_indirectModUseExt;
v___x_319_ = 0;
v___x_320_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_317_, v___x_318_, v_env_315_, v_modIdx_316_, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object* v_env_321_, lean_object* v_modIdx_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_getIndirectModUses(v_env_321_, v_modIdx_322_);
lean_dec(v_modIdx_322_);
lean_dec_ref(v_env_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object* v___x_324_, lean_object* v___x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_toEnvExtension_327_; lean_object* v_asyncMode_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_toEnvExtension_327_ = lean_ctor_get(v___x_324_, 0);
v_asyncMode_328_ = lean_ctor_get(v_toEnvExtension_327_, 2);
lean_inc(v_asyncMode_328_);
v___x_329_ = lean_box(0);
v___x_330_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_324_, v_x_326_, v___x_325_, v_asyncMode_328_, v___x_329_);
lean_dec(v_asyncMode_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object* v_modifyEnv_331_, lean_object* v___f_332_, lean_object* v_____r_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_apply_1(v_modifyEnv_331_, v___f_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object* v_toPure_338_, lean_object* v_cls_339_, lean_object* v_____do__lift_340_, lean_object* v_____do__lift_341_){
_start:
{
uint8_t v_hasTrace_342_; 
v_hasTrace_342_ = lean_ctor_get_uint8(v_____do__lift_341_, sizeof(void*)*1);
if (v_hasTrace_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_cls_339_);
v___x_343_ = lean_box(v_hasTrace_342_);
v___x_344_ = lean_apply_2(v_toPure_338_, lean_box(0), v___x_343_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_345_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__1));
v___x_346_ = l_Lean_Name_append(v___x_345_, v_cls_339_);
v___x_347_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_340_, v_____do__lift_341_, v___x_346_);
lean_dec(v___x_346_);
v___x_348_ = lean_box(v___x_347_);
v___x_349_ = lean_apply_2(v_toPure_338_, lean_box(0), v___x_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object* v_toPure_350_, lean_object* v_cls_351_, lean_object* v_____do__lift_352_, lean_object* v_____do__lift_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_toPure_350_, v_cls_351_, v_____do__lift_352_, v_____do__lift_353_);
lean_dec_ref(v_____do__lift_353_);
lean_dec_ref(v_____do__lift_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v_toPure_355_, lean_object* v_cls_356_, lean_object* v_toBind_357_, lean_object* v_inst_358_, lean_object* v_____do__lift_359_){
_start:
{
lean_object* v___f_360_; lean_object* v___x_361_; 
v___f_360_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_360_, 0, v_toPure_355_);
lean_closure_set(v___f_360_, 1, v_cls_356_);
lean_closure_set(v___f_360_, 2, v_____do__lift_359_);
v___x_361_ = lean_apply_4(v_toBind_357_, lean_box(0), lean_box(0), v_inst_358_, v___f_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__4___closed__0));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__3(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__4___closed__2));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__5(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__4___closed__4));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object* v_modifyEnv_371_, lean_object* v___f_372_, lean_object* v_declName_373_, lean_object* v_kind_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_cls_379_, lean_object* v_toBind_380_, lean_object* v___f_381_, uint8_t v_____do__lift_382_){
_start:
{
if (v_____do__lift_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v___f_381_);
lean_dec(v_toBind_380_);
lean_dec(v_cls_379_);
lean_dec(v_inst_378_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
lean_dec_ref(v_inst_375_);
lean_dec_ref(v_kind_374_);
lean_dec(v_declName_373_);
v___x_383_ = lean_apply_1(v_modifyEnv_371_, v___f_372_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v___f_372_);
lean_dec(v_modifyEnv_371_);
v___x_384_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__4___closed__1, &l_Lean_recordIndirectModUse___redArg___lam__4___closed__1_once, _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__1);
v___x_385_ = l_Lean_MessageData_ofName(v_declName_373_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__4___closed__3, &l_Lean_recordIndirectModUse___redArg___lam__4___closed__3_once, _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__3);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_stringToMessageData(v_kind_374_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__4___closed__5, &l_Lean_recordIndirectModUse___redArg___lam__4___closed__5_once, _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__5);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_addTrace___redArg(v_inst_375_, v_inst_376_, v_inst_377_, v_inst_378_, v_cls_379_, v___x_392_);
v___x_394_ = lean_apply_4(v_toBind_380_, lean_box(0), lean_box(0), v___x_393_, v___f_381_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___boxed(lean_object* v_modifyEnv_395_, lean_object* v___f_396_, lean_object* v_declName_397_, lean_object* v_kind_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_cls_403_, lean_object* v_toBind_404_, lean_object* v___f_405_, lean_object* v_____do__lift_406_){
_start:
{
uint8_t v_____do__lift_440__boxed_407_; lean_object* v_res_408_; 
v_____do__lift_440__boxed_407_ = lean_unbox(v_____do__lift_406_);
v_res_408_ = l_Lean_recordIndirectModUse___redArg___lam__4(v_modifyEnv_395_, v___f_396_, v_declName_397_, v_kind_398_, v_inst_399_, v_inst_400_, v_inst_401_, v_inst_402_, v_cls_403_, v_toBind_404_, v___f_405_, v_____do__lift_440__boxed_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v___x_412_, lean_object* v_kind_413_, lean_object* v_declName_414_, lean_object* v___x_415_, lean_object* v_inst_416_, lean_object* v_modifyEnv_417_, lean_object* v_toPure_418_, lean_object* v_toBind_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_____do__lift_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_425_ = l_Lean_indirectModUseExt;
v___x_426_ = lean_box(2);
v___x_427_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_412_, v___x_425_, v_____do__lift_424_, v___x_426_);
lean_inc(v_declName_414_);
lean_inc_ref(v_kind_413_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_kind_413_);
lean_ctor_set(v___x_428_, 1, v_declName_414_);
lean_inc_ref(v___x_428_);
v___x_429_ = l_List_elem___redArg(v___x_415_, v___x_428_, v___x_427_);
if (v___x_429_ == 0)
{
lean_object* v_getInheritedTraceOptions_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v_cls_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_getInheritedTraceOptions_430_ = lean_ctor_get(v_inst_416_, 2);
lean_inc(v_getInheritedTraceOptions_430_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_431_, 0, v___x_425_);
lean_closure_set(v___f_431_, 1, v___x_428_);
lean_inc_ref(v___f_431_);
lean_inc(v_modifyEnv_417_);
v___f_432_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_432_, 0, v_modifyEnv_417_);
lean_closure_set(v___f_432_, 1, v___f_431_);
v_cls_433_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_419_, 3);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 5, 4);
lean_closure_set(v___f_434_, 0, v_toPure_418_);
lean_closure_set(v___f_434_, 1, v_cls_433_);
lean_closure_set(v___f_434_, 2, v_toBind_419_);
lean_closure_set(v___f_434_, 3, v_inst_420_);
v___f_435_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_435_, 0, v_modifyEnv_417_);
lean_closure_set(v___f_435_, 1, v___f_431_);
lean_closure_set(v___f_435_, 2, v_declName_414_);
lean_closure_set(v___f_435_, 3, v_kind_413_);
lean_closure_set(v___f_435_, 4, v_inst_421_);
lean_closure_set(v___f_435_, 5, v_inst_416_);
lean_closure_set(v___f_435_, 6, v_inst_422_);
lean_closure_set(v___f_435_, 7, v_inst_423_);
lean_closure_set(v___f_435_, 8, v_cls_433_);
lean_closure_set(v___f_435_, 9, v_toBind_419_);
lean_closure_set(v___f_435_, 10, v___f_432_);
v___x_436_ = lean_apply_4(v_toBind_419_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_430_, v___f_434_);
v___x_437_ = lean_apply_4(v_toBind_419_, lean_box(0), lean_box(0), v___x_436_, v___f_435_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref_known(v___x_428_, 2);
lean_dec(v_inst_423_);
lean_dec_ref(v_inst_422_);
lean_dec_ref(v_inst_421_);
lean_dec(v_inst_420_);
lean_dec(v_toBind_419_);
lean_dec(v_modifyEnv_417_);
lean_dec_ref(v_inst_416_);
lean_dec(v_declName_414_);
lean_dec_ref(v_kind_413_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_kind_446_, lean_object* v_declName_447_){
_start:
{
lean_object* v_toApplicative_448_; lean_object* v_toBind_449_; lean_object* v_getEnv_450_; lean_object* v_modifyEnv_451_; lean_object* v_toPure_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v_toApplicative_448_ = lean_ctor_get(v_inst_440_, 0);
v_toBind_449_ = lean_ctor_get(v_inst_440_, 1);
lean_inc_n(v_toBind_449_, 2);
v_getEnv_450_ = lean_ctor_get(v_inst_441_, 0);
lean_inc(v_getEnv_450_);
v_modifyEnv_451_ = lean_ctor_get(v_inst_441_, 1);
lean_inc(v_modifyEnv_451_);
lean_dec_ref(v_inst_441_);
v_toPure_452_ = lean_ctor_get(v_toApplicative_448_, 1);
lean_inc(v_toPure_452_);
v___x_453_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_454_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5), 13, 12);
lean_closure_set(v___f_455_, 0, v___x_454_);
lean_closure_set(v___f_455_, 1, v_kind_446_);
lean_closure_set(v___f_455_, 2, v_declName_447_);
lean_closure_set(v___f_455_, 3, v___x_453_);
lean_closure_set(v___f_455_, 4, v_inst_442_);
lean_closure_set(v___f_455_, 5, v_modifyEnv_451_);
lean_closure_set(v___f_455_, 6, v_toPure_452_);
lean_closure_set(v___f_455_, 7, v_toBind_449_);
lean_closure_set(v___f_455_, 8, v_inst_443_);
lean_closure_set(v___f_455_, 9, v_inst_440_);
lean_closure_set(v___f_455_, 10, v_inst_444_);
lean_closure_set(v___f_455_, 11, v_inst_445_);
v___x_456_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v_getEnv_450_, v___f_455_);
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
if (v_isExported_473_ == 0)
{
if (v_isExported_470_ == 0)
{
v___y_476_ = v___x_477_;
goto v___jp_475_;
}
else
{
return v_isExported_473_;
}
}
else
{
v___y_476_ = v_isExported_470_;
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
if (v_isMeta_474_ == 0)
{
if (v_isMeta_471_ == 0)
{
return v___y_476_;
}
else
{
return v_isMeta_474_;
}
}
else
{
return v_isMeta_471_;
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
lean_object* v_ks_706_; lean_object* v_vs_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_725_; 
v_ks_706_ = lean_ctor_get(v_x_655_, 0);
v_vs_707_ = lean_ctor_get(v_x_655_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_725_ == 0)
{
v___x_709_ = v_x_655_;
v_isShared_710_ = v_isSharedCheck_725_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_vs_707_);
lean_inc(v_ks_706_);
lean_dec(v_x_655_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_725_;
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
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_ks_706_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_vs_707_);
v___x_712_ = v_reuseFailAlloc_724_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v_newNode_713_; size_t v___x_714_; uint8_t v___x_715_; 
v_newNode_713_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_712_, v_x_658_, v_x_659_);
v___x_714_ = ((size_t)7ULL);
v___x_715_ = lean_usize_dec_le(v___x_714_, v_x_657_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_713_);
v___x_717_ = lean_unsigned_to_nat(4u);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
lean_dec(v___x_716_);
if (v___x_718_ == 0)
{
lean_object* v_ks_719_; lean_object* v_vs_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_ks_719_ = lean_ctor_get(v_newNode_713_, 0);
lean_inc_ref(v_ks_719_);
v_vs_720_ = lean_ctor_get(v_newNode_713_, 1);
lean_inc_ref(v_vs_720_);
lean_dec_ref(v_newNode_713_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_723_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_657_, v_ks_719_, v_vs_720_, v___x_721_, v___x_722_);
lean_dec_ref(v_vs_720_);
lean_dec_ref(v_ks_719_);
return v___x_723_;
}
else
{
return v_newNode_713_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_726_, lean_object* v_keys_727_, lean_object* v_vals_728_, lean_object* v_i_729_, lean_object* v_entries_730_){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_keys_727_);
v___x_732_ = lean_nat_dec_lt(v_i_729_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_i_729_);
return v_entries_730_;
}
else
{
lean_object* v_k_733_; lean_object* v_v_734_; uint64_t v___x_735_; size_t v_h_736_; size_t v___x_737_; lean_object* v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v_h_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_k_733_ = lean_array_fget_borrowed(v_keys_727_, v_i_729_);
v_v_734_ = lean_array_fget_borrowed(v_vals_728_, v_i_729_);
v___x_735_ = l_Lean_instHashableExtraModUse_hash(v_k_733_);
v_h_736_ = lean_uint64_to_usize(v___x_735_);
v___x_737_ = ((size_t)5ULL);
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_sub(v_depth_726_, v___x_739_);
v___x_741_ = lean_usize_mul(v___x_737_, v___x_740_);
v_h_742_ = lean_usize_shift_right(v_h_736_, v___x_741_);
v___x_743_ = lean_nat_add(v_i_729_, v___x_738_);
lean_dec(v_i_729_);
lean_inc(v_v_734_);
lean_inc(v_k_733_);
v___x_744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_730_, v_h_742_, v_depth_726_, v_k_733_, v_v_734_);
v_i_729_ = v___x_743_;
v_entries_730_ = v___x_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_746_, lean_object* v_keys_747_, lean_object* v_vals_748_, lean_object* v_i_749_, lean_object* v_entries_750_){
_start:
{
size_t v_depth_boxed_751_; lean_object* v_res_752_; 
v_depth_boxed_751_ = lean_unbox_usize(v_depth_746_);
lean_dec(v_depth_746_);
v_res_752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_751_, v_keys_747_, v_vals_748_, v_i_749_, v_entries_750_);
lean_dec_ref(v_vals_748_);
lean_dec_ref(v_keys_747_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
size_t v_x_571__boxed_758_; size_t v_x_572__boxed_759_; lean_object* v_res_760_; 
v_x_571__boxed_758_ = lean_unbox_usize(v_x_754_);
lean_dec(v_x_754_);
v_x_572__boxed_759_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_res_760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_753_, v_x_571__boxed_758_, v_x_572__boxed_759_, v_x_756_, v_x_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
uint64_t v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_764_ = l_Lean_instHashableExtraModUse_hash(v_x_762_);
v___x_765_ = lean_uint64_to_usize(v___x_764_);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_761_, v___x_765_, v___x_766_, v_x_762_, v_x_763_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_768_, lean_object* v_k_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_768_, v_k_769_, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_772_, lean_object* v_i_773_, lean_object* v_k_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_array_get_size(v_keys_772_);
v___x_776_ = lean_nat_dec_lt(v_i_773_, v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v_i_773_);
return v___x_776_;
}
else
{
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_keys_772_, v_i_773_);
v___x_778_ = l_Lean_instBEqExtraModUse_beq(v_k_774_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_i_773_, v___x_779_);
lean_dec(v_i_773_);
v_i_773_ = v___x_780_;
goto _start;
}
else
{
lean_dec(v_i_773_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_782_, v_i_783_, v_k_784_);
lean_dec_ref(v_k_784_);
lean_dec_ref(v_keys_782_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_787_) == 0)
{
lean_object* v_es_790_; lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_j_794_; lean_object* v___x_795_; 
v_es_790_ = lean_ctor_get(v_x_787_, 0);
v___x_791_ = lean_box(2);
v___x_792_ = ((size_t)31ULL);
v___x_793_ = lean_usize_land(v_x_788_, v___x_792_);
v_j_794_ = lean_usize_to_nat(v___x_793_);
v___x_795_ = lean_array_get_borrowed(v___x_791_, v_es_790_, v_j_794_);
lean_dec(v_j_794_);
switch(lean_obj_tag(v___x_795_))
{
case 0:
{
lean_object* v_key_796_; uint8_t v___x_797_; 
v_key_796_ = lean_ctor_get(v___x_795_, 0);
v___x_797_ = l_Lean_instBEqExtraModUse_beq(v_x_789_, v_key_796_);
return v___x_797_;
}
case 1:
{
lean_object* v_node_798_; size_t v___x_799_; size_t v___x_800_; 
v_node_798_ = lean_ctor_get(v___x_795_, 0);
v___x_799_ = ((size_t)5ULL);
v___x_800_ = lean_usize_shift_right(v_x_788_, v___x_799_);
v_x_787_ = v_node_798_;
v_x_788_ = v___x_800_;
goto _start;
}
default: 
{
uint8_t v___x_802_; 
v___x_802_ = 0;
return v___x_802_;
}
}
}
else
{
lean_object* v_ks_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_ks_803_ = lean_ctor_get(v_x_787_, 0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_803_, v___x_804_, v_x_789_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_753__boxed_809_; uint8_t v_res_810_; lean_object* v_r_811_; 
v_x_753__boxed_809_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_810_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_806_, v_x_753__boxed_809_, v_x_808_);
lean_dec_ref(v_x_808_);
lean_dec_ref(v_x_806_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
uint64_t v___x_814_; size_t v___x_815_; uint8_t v___x_816_; 
v___x_814_ = l_Lean_instHashableExtraModUse_hash(v_x_813_);
v___x_815_ = lean_uint64_to_usize(v___x_814_);
v___x_816_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_812_, v___x_815_, v_x_813_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_817_, v_x_818_);
lean_dec_ref(v_x_818_);
lean_dec_ref(v_x_817_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_863_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_867_, v_x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_870_, v_x_871_, v_x_872_);
lean_dec_ref(v_x_872_);
lean_dec_ref(v_x_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_876_, v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, size_t v_x_882_, lean_object* v_x_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
size_t v_x_951__boxed_889_; uint8_t v_res_890_; lean_object* v_r_891_; 
v_x_951__boxed_889_ = lean_unbox_usize(v_x_887_);
lean_dec(v_x_887_);
v_res_890_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_885_, v_x_886_, v_x_951__boxed_889_, v_x_888_);
lean_dec_ref(v_x_888_);
lean_dec_ref(v_x_886_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, size_t v_x_894_, size_t v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_893_, v_x_894_, v_x_895_, v_x_896_, v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_962__boxed_905_; size_t v_x_963__boxed_906_; lean_object* v_res_907_; 
v_x_962__boxed_905_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_x_963__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_899_, v_x_900_, v_x_962__boxed_905_, v_x_963__boxed_906_, v_x_903_, v_x_904_);
return v_res_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_908_, lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_heq_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_909_, v_i_912_, v_k_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_915_, lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_heq_918_, lean_object* v_i_919_, lean_object* v_k_920_){
_start:
{
uint8_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_915_, v_keys_916_, v_vals_917_, v_heq_918_, v_i_919_, v_k_920_);
lean_dec_ref(v_k_920_);
lean_dec_ref(v_vals_917_);
lean_dec_ref(v_keys_916_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_923_, lean_object* v_n_924_, lean_object* v_k_925_, lean_object* v_v_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_924_, v_k_925_, v_v_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_928_, size_t v_depth_929_, lean_object* v_keys_930_, lean_object* v_vals_931_, lean_object* v_heq_932_, lean_object* v_i_933_, lean_object* v_entries_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_929_, v_keys_930_, v_vals_931_, v_i_933_, v_entries_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_936_, lean_object* v_depth_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_entries_942_){
_start:
{
size_t v_depth_boxed_943_; lean_object* v_res_944_; 
v_depth_boxed_943_ = lean_unbox_usize(v_depth_937_);
lean_dec(v_depth_937_);
v_res_944_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_936_, v_depth_boxed_943_, v_keys_938_, v_vals_939_, v_heq_940_, v_i_941_, v_entries_942_);
lean_dec_ref(v_vals_939_);
lean_dec_ref(v_keys_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_946_, v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_952_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_953_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_952_, v___x_951_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_955_ = lean_box(0);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_957_, lean_object* v_modIdx_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; 
v___x_959_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_960_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_961_ = 0;
v___x_962_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_959_, v___x_960_, v_env_957_, v_modIdx_958_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_963_, lean_object* v_modIdx_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_getExtraModUses(v_env_963_, v_modIdx_964_);
lean_dec(v_modIdx_964_);
lean_dec_ref(v_env_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_966_, lean_object* v_b_967_){
_start:
{
if (lean_obj_tag(v_as_x27_966_) == 0)
{
return v_b_967_;
}
else
{
lean_object* v_head_968_; lean_object* v_tail_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_head_968_ = lean_ctor_get(v_as_x27_966_, 0);
v_tail_969_ = lean_ctor_get(v_as_x27_966_, 1);
v___x_970_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_971_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_972_ = lean_box(1);
v___x_973_ = lean_box(0);
lean_inc_ref(v_b_967_);
v___x_974_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_970_, v___x_971_, v_b_967_, v___x_972_, v___x_973_);
v___x_975_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_974_, v_head_968_);
lean_dec(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v_toEnvExtension_976_; lean_object* v_asyncMode_977_; lean_object* v___x_978_; 
v_toEnvExtension_976_ = lean_ctor_get(v___x_971_, 0);
v_asyncMode_977_ = lean_ctor_get(v_toEnvExtension_976_, 2);
lean_inc(v_head_968_);
v___x_978_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_971_, v_b_967_, v_head_968_, v_asyncMode_977_, v___x_973_);
v_as_x27_966_ = v_tail_969_;
v_b_967_ = v___x_978_;
goto _start;
}
else
{
v_as_x27_966_ = v_tail_969_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_981_, lean_object* v_b_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_981_, v_b_982_);
lean_dec(v_as_x27_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_984_, lean_object* v_dest_985_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_986_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_987_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_988_ = lean_box(1);
v___x_989_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_986_, v___x_987_, v_src_984_, v___x_988_);
v___x_990_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_989_, v_dest_985_);
lean_dec(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_991_, lean_object* v_as_x27_992_, lean_object* v_b_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_992_, v_b_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_996_, lean_object* v_as_x27_997_, lean_object* v_b_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_996_, v_as_x27_997_, v_b_998_, v_a_999_);
lean_dec(v_as_x27_997_);
lean_dec(v_as_996_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1001_, lean_object* v_entry_1002_, lean_object* v___x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_toEnvExtension_1005_; lean_object* v_asyncMode_1006_; lean_object* v___x_1007_; 
v_toEnvExtension_1005_ = lean_ctor_get(v___x_1001_, 0);
v_asyncMode_1006_ = lean_ctor_get(v_toEnvExtension_1005_, 2);
lean_inc(v_asyncMode_1006_);
v___x_1007_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1001_, v_x_1004_, v_entry_1002_, v_asyncMode_1006_, v___x_1003_);
lean_dec(v_asyncMode_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v_modifyEnv_1027_, lean_object* v___f_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_cls_1033_, lean_object* v_toBind_1034_, lean_object* v___f_1035_, lean_object* v_mod_1036_, lean_object* v_hint_1037_, uint8_t v_isMeta_1038_, uint8_t v_isExporting_1039_, uint8_t v_____do__lift_1040_){
_start:
{
lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1048_; lean_object* v___y_1049_; 
if (v_____do__lift_1040_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v_hint_1037_);
lean_dec(v_mod_1036_);
lean_dec(v___f_1035_);
lean_dec(v_toBind_1034_);
lean_dec(v_cls_1033_);
lean_dec(v_inst_1032_);
lean_dec_ref(v_inst_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
v___x_1061_ = lean_apply_1(v_modifyEnv_1027_, v___f_1028_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; lean_object* v___y_1064_; 
lean_dec_ref(v___f_1028_);
lean_dec(v_modifyEnv_1027_);
v___x_1062_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7);
if (v_isExporting_1039_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12));
v___y_1064_ = v___x_1071_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13));
v___y_1064_ = v___x_1072_;
goto v___jp_1063_;
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_inc_ref(v___y_1064_);
v___x_1065_ = l_Lean_stringToMessageData(v___y_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1062_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
if (v_isMeta_1038_ == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10));
v___y_1048_ = v___x_1068_;
v___y_1049_ = v___x_1069_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1070_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11));
v___y_1048_ = v___x_1068_;
v___y_1049_ = v___x_1070_;
goto v___jp_1047_;
}
}
}
v___jp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___y_1042_);
lean_ctor_set(v___x_1044_, 1, v___y_1043_);
v___x_1045_ = l_Lean_addTrace___redArg(v_inst_1029_, v_inst_1030_, v_inst_1031_, v_inst_1032_, v_cls_1033_, v___x_1044_);
v___x_1046_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1045_, v___f_1035_);
return v___x_1046_;
}
v___jp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
lean_inc_ref(v___y_1049_);
v___x_1050_ = l_Lean_stringToMessageData(v___y_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___y_1048_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_MessageData_ofName(v_mod_1036_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_Name_isAnonymous(v_hint_1037_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3);
v___x_1058_ = l_Lean_MessageData_ofName(v_hint_1037_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___y_1042_ = v___x_1055_;
v___y_1043_ = v___x_1059_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1060_; 
lean_dec(v_hint_1037_);
v___x_1060_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5);
v___y_1042_ = v___x_1055_;
v___y_1043_ = v___x_1060_;
goto v___jp_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object* v_modifyEnv_1073_, lean_object* v___f_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_cls_1079_, lean_object* v_toBind_1080_, lean_object* v___f_1081_, lean_object* v_mod_1082_, lean_object* v_hint_1083_, lean_object* v_isMeta_1084_, lean_object* v_isExporting_1085_, lean_object* v_____do__lift_1086_){
_start:
{
uint8_t v_isMeta_boxed_1087_; uint8_t v_isExporting_boxed_1088_; uint8_t v_____do__lift_550__boxed_1089_; lean_object* v_res_1090_; 
v_isMeta_boxed_1087_ = lean_unbox(v_isMeta_1084_);
v_isExporting_boxed_1088_ = lean_unbox(v_isExporting_1085_);
v_____do__lift_550__boxed_1089_ = lean_unbox(v_____do__lift_1086_);
v_res_1090_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v_modifyEnv_1073_, v___f_1074_, v_inst_1075_, v_inst_1076_, v_inst_1077_, v_inst_1078_, v_cls_1079_, v_toBind_1080_, v___f_1081_, v_mod_1082_, v_hint_1083_, v_isMeta_boxed_1087_, v_isExporting_boxed_1088_, v_____do__lift_550__boxed_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v_entry_1094_, lean_object* v_inst_1095_, lean_object* v_modifyEnv_1096_, lean_object* v_toPure_1097_, lean_object* v_toBind_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_mod_1103_, lean_object* v_hint_1104_, uint8_t v_isMeta_1105_, uint8_t v_isExporting_1106_, lean_object* v_____do__lift_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1108_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1109_ = lean_box(1);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1091_, v___x_1108_, v_____do__lift_1107_, v___x_1109_, v___x_1110_);
lean_inc_ref(v_entry_1094_);
v___x_1112_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1092_, v___x_1093_, v___x_1111_, v_entry_1094_);
if (v___x_1112_ == 0)
{
lean_object* v_getInheritedTraceOptions_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v_cls_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_getInheritedTraceOptions_1113_ = lean_ctor_get(v_inst_1095_, 2);
lean_inc(v_getInheritedTraceOptions_1113_);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1114_, 0, v___x_1108_);
lean_closure_set(v___f_1114_, 1, v_entry_1094_);
lean_closure_set(v___f_1114_, 2, v___x_1110_);
lean_inc_ref(v___f_1114_);
lean_inc(v_modifyEnv_1096_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1115_, 0, v_modifyEnv_1096_);
lean_closure_set(v___f_1115_, 1, v___f_1114_);
v_cls_1116_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1098_, 3);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1117_, 0, v_toPure_1097_);
lean_closure_set(v___f_1117_, 1, v_cls_1116_);
lean_closure_set(v___f_1117_, 2, v_toBind_1098_);
lean_closure_set(v___f_1117_, 3, v_inst_1099_);
v___x_1118_ = lean_box(v_isMeta_1105_);
v___x_1119_ = lean_box(v_isExporting_1106_);
v___f_1120_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_1120_, 0, v_modifyEnv_1096_);
lean_closure_set(v___f_1120_, 1, v___f_1114_);
lean_closure_set(v___f_1120_, 2, v_inst_1100_);
lean_closure_set(v___f_1120_, 3, v_inst_1095_);
lean_closure_set(v___f_1120_, 4, v_inst_1101_);
lean_closure_set(v___f_1120_, 5, v_inst_1102_);
lean_closure_set(v___f_1120_, 6, v_cls_1116_);
lean_closure_set(v___f_1120_, 7, v_toBind_1098_);
lean_closure_set(v___f_1120_, 8, v___f_1115_);
lean_closure_set(v___f_1120_, 9, v_mod_1103_);
lean_closure_set(v___f_1120_, 10, v_hint_1104_);
lean_closure_set(v___f_1120_, 11, v___x_1118_);
lean_closure_set(v___f_1120_, 12, v___x_1119_);
v___x_1121_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1113_, v___f_1117_);
v___x_1122_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1121_, v___f_1120_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec(v_hint_1104_);
lean_dec(v_mod_1103_);
lean_dec(v_inst_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec(v_inst_1099_);
lean_dec(v_toBind_1098_);
lean_dec(v_modifyEnv_1096_);
lean_dec_ref(v_inst_1095_);
lean_dec_ref(v_entry_1094_);
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_apply_2(v_toPure_1097_, lean_box(0), v___x_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1125_ = _args[0];
lean_object* v___x_1126_ = _args[1];
lean_object* v___x_1127_ = _args[2];
lean_object* v_entry_1128_ = _args[3];
lean_object* v_inst_1129_ = _args[4];
lean_object* v_modifyEnv_1130_ = _args[5];
lean_object* v_toPure_1131_ = _args[6];
lean_object* v_toBind_1132_ = _args[7];
lean_object* v_inst_1133_ = _args[8];
lean_object* v_inst_1134_ = _args[9];
lean_object* v_inst_1135_ = _args[10];
lean_object* v_inst_1136_ = _args[11];
lean_object* v_mod_1137_ = _args[12];
lean_object* v_hint_1138_ = _args[13];
lean_object* v_isMeta_1139_ = _args[14];
lean_object* v_isExporting_1140_ = _args[15];
lean_object* v_____do__lift_1141_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1142_; uint8_t v_isExporting_boxed_1143_; lean_object* v_res_1144_; 
v_isMeta_boxed_1142_ = lean_unbox(v_isMeta_1139_);
v_isExporting_boxed_1143_ = lean_unbox(v_isExporting_1140_);
v_res_1144_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v___x_1125_, v___x_1126_, v___x_1127_, v_entry_1128_, v_inst_1129_, v_modifyEnv_1130_, v_toPure_1131_, v_toBind_1132_, v_inst_1133_, v_inst_1134_, v_inst_1135_, v_inst_1136_, v_mod_1137_, v_hint_1138_, v_isMeta_boxed_1142_, v_isExporting_boxed_1143_, v_____do__lift_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_mod_1145_, uint8_t v_isMeta_1146_, lean_object* v___x_1147_, lean_object* v___x_1148_, lean_object* v___x_1149_, lean_object* v_inst_1150_, lean_object* v_modifyEnv_1151_, lean_object* v_toPure_1152_, lean_object* v_toBind_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_hint_1158_, lean_object* v_getEnv_1159_, lean_object* v_____do__lift_1160_){
_start:
{
uint8_t v_isExporting_1161_; lean_object* v_entry_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v_isExporting_1161_ = lean_ctor_get_uint8(v_____do__lift_1160_, sizeof(void*)*8);
lean_inc(v_mod_1145_);
v_entry_1162_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1162_, 0, v_mod_1145_);
lean_ctor_set_uint8(v_entry_1162_, sizeof(void*)*1, v_isExporting_1161_);
lean_ctor_set_uint8(v_entry_1162_, sizeof(void*)*1 + 1, v_isMeta_1146_);
v___x_1163_ = lean_box(v_isMeta_1146_);
v___x_1164_ = lean_box(v_isExporting_1161_);
lean_inc(v_toBind_1153_);
v___f_1165_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 17, 16);
lean_closure_set(v___f_1165_, 0, v___x_1147_);
lean_closure_set(v___f_1165_, 1, v___x_1148_);
lean_closure_set(v___f_1165_, 2, v___x_1149_);
lean_closure_set(v___f_1165_, 3, v_entry_1162_);
lean_closure_set(v___f_1165_, 4, v_inst_1150_);
lean_closure_set(v___f_1165_, 5, v_modifyEnv_1151_);
lean_closure_set(v___f_1165_, 6, v_toPure_1152_);
lean_closure_set(v___f_1165_, 7, v_toBind_1153_);
lean_closure_set(v___f_1165_, 8, v_inst_1154_);
lean_closure_set(v___f_1165_, 9, v_inst_1155_);
lean_closure_set(v___f_1165_, 10, v_inst_1156_);
lean_closure_set(v___f_1165_, 11, v_inst_1157_);
lean_closure_set(v___f_1165_, 12, v_mod_1145_);
lean_closure_set(v___f_1165_, 13, v_hint_1158_);
lean_closure_set(v___f_1165_, 14, v___x_1163_);
lean_closure_set(v___f_1165_, 15, v___x_1164_);
v___x_1166_ = lean_apply_4(v_toBind_1153_, lean_box(0), lean_box(0), v_getEnv_1159_, v___f_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_mod_1167_, lean_object* v_isMeta_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v___x_1171_, lean_object* v_inst_1172_, lean_object* v_modifyEnv_1173_, lean_object* v_toPure_1174_, lean_object* v_toBind_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_hint_1180_, lean_object* v_getEnv_1181_, lean_object* v_____do__lift_1182_){
_start:
{
uint8_t v_isMeta_boxed_1183_; lean_object* v_res_1184_; 
v_isMeta_boxed_1183_ = lean_unbox(v_isMeta_1168_);
v_res_1184_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_mod_1167_, v_isMeta_boxed_1183_, v___x_1169_, v___x_1170_, v___x_1171_, v_inst_1172_, v_modifyEnv_1173_, v_toPure_1174_, v_toBind_1175_, v_inst_1176_, v_inst_1177_, v_inst_1178_, v_inst_1179_, v_hint_1180_, v_getEnv_1181_, v_____do__lift_1182_);
lean_dec_ref(v_____do__lift_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_mod_1191_, uint8_t v_isMeta_1192_, lean_object* v_hint_1193_){
_start:
{
lean_object* v_toApplicative_1194_; lean_object* v_toBind_1195_; lean_object* v_getEnv_1196_; lean_object* v_modifyEnv_1197_; lean_object* v_toPure_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; 
v_toApplicative_1194_ = lean_ctor_get(v_inst_1185_, 0);
v_toBind_1195_ = lean_ctor_get(v_inst_1185_, 1);
lean_inc_n(v_toBind_1195_, 2);
v_getEnv_1196_ = lean_ctor_get(v_inst_1186_, 0);
lean_inc_n(v_getEnv_1196_, 2);
v_modifyEnv_1197_ = lean_ctor_get(v_inst_1186_, 1);
lean_inc(v_modifyEnv_1197_);
lean_dec_ref(v_inst_1186_);
v_toPure_1198_ = lean_ctor_get(v_toApplicative_1194_, 1);
lean_inc(v_toPure_1198_);
v___x_1199_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1200_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1201_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1202_ = lean_box(v_isMeta_1192_);
v___f_1203_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 16, 15);
lean_closure_set(v___f_1203_, 0, v_mod_1191_);
lean_closure_set(v___f_1203_, 1, v___x_1202_);
lean_closure_set(v___f_1203_, 2, v___x_1201_);
lean_closure_set(v___f_1203_, 3, v___x_1199_);
lean_closure_set(v___f_1203_, 4, v___x_1200_);
lean_closure_set(v___f_1203_, 5, v_inst_1187_);
lean_closure_set(v___f_1203_, 6, v_modifyEnv_1197_);
lean_closure_set(v___f_1203_, 7, v_toPure_1198_);
lean_closure_set(v___f_1203_, 8, v_toBind_1195_);
lean_closure_set(v___f_1203_, 9, v_inst_1188_);
lean_closure_set(v___f_1203_, 10, v_inst_1185_);
lean_closure_set(v___f_1203_, 11, v_inst_1189_);
lean_closure_set(v___f_1203_, 12, v_inst_1190_);
lean_closure_set(v___f_1203_, 13, v_hint_1193_);
lean_closure_set(v___f_1203_, 14, v_getEnv_1196_);
v___x_1204_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v_getEnv_1196_, v___f_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_mod_1211_, lean_object* v_isMeta_1212_, lean_object* v_hint_1213_){
_start:
{
uint8_t v_isMeta_boxed_1214_; lean_object* v_res_1215_; 
v_isMeta_boxed_1214_ = lean_unbox(v_isMeta_1212_);
v_res_1215_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1205_, v_inst_1206_, v_inst_1207_, v_inst_1208_, v_inst_1209_, v_inst_1210_, v_mod_1211_, v_isMeta_boxed_1214_, v_hint_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_mod_1223_, uint8_t v_isMeta_1224_, lean_object* v_hint_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1217_, v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_mod_1223_, v_isMeta_1224_, v_hint_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_mod_1234_, lean_object* v_isMeta_1235_, lean_object* v_hint_1236_){
_start:
{
uint8_t v_isMeta_boxed_1237_; lean_object* v_res_1238_; 
v_isMeta_boxed_1237_ = lean_unbox(v_isMeta_1235_);
v_res_1238_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1227_, v_inst_1228_, v_inst_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_mod_1234_, v_isMeta_boxed_1237_, v_hint_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, uint8_t v_isMeta_1246_, lean_object* v_toPure_1247_, lean_object* v_____do__lift_1248_){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = l_Lean_Environment_mainModule(v_____do__lift_1248_);
v___x_1250_ = lean_name_eq(v_modName_1239_, v___x_1249_);
lean_dec(v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec(v_toPure_1247_);
v___x_1251_ = lean_box(0);
v___x_1252_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1240_, v_inst_1241_, v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v_modName_1239_, v_isMeta_1246_, v___x_1251_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_inst_1245_);
lean_dec_ref(v_inst_1244_);
lean_dec(v_inst_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec(v_modName_1239_);
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_apply_2(v_toPure_1247_, lean_box(0), v___x_1253_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_isMeta_1262_, lean_object* v_toPure_1263_, lean_object* v_____do__lift_1264_){
_start:
{
uint8_t v_isMeta_boxed_1265_; lean_object* v_res_1266_; 
v_isMeta_boxed_1265_ = lean_unbox(v_isMeta_1262_);
v_res_1266_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_inst_1260_, v_inst_1261_, v_isMeta_boxed_1265_, v_toPure_1263_, v_____do__lift_1264_);
lean_dec_ref(v_____do__lift_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_modName_1273_, uint8_t v_isMeta_1274_){
_start:
{
lean_object* v_toApplicative_1275_; lean_object* v_toBind_1276_; lean_object* v_getEnv_1277_; lean_object* v_toPure_1278_; lean_object* v___x_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; 
v_toApplicative_1275_ = lean_ctor_get(v_inst_1267_, 0);
v_toBind_1276_ = lean_ctor_get(v_inst_1267_, 1);
lean_inc(v_toBind_1276_);
v_getEnv_1277_ = lean_ctor_get(v_inst_1268_, 0);
lean_inc(v_getEnv_1277_);
v_toPure_1278_ = lean_ctor_get(v_toApplicative_1275_, 1);
lean_inc(v_toPure_1278_);
v___x_1279_ = lean_box(v_isMeta_1274_);
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1280_, 0, v_modName_1273_);
lean_closure_set(v___f_1280_, 1, v_inst_1267_);
lean_closure_set(v___f_1280_, 2, v_inst_1268_);
lean_closure_set(v___f_1280_, 3, v_inst_1269_);
lean_closure_set(v___f_1280_, 4, v_inst_1270_);
lean_closure_set(v___f_1280_, 5, v_inst_1271_);
lean_closure_set(v___f_1280_, 6, v_inst_1272_);
lean_closure_set(v___f_1280_, 7, v___x_1279_);
lean_closure_set(v___f_1280_, 8, v_toPure_1278_);
v___x_1281_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v_getEnv_1277_, v___f_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_modName_1288_, lean_object* v_isMeta_1289_){
_start:
{
uint8_t v_isMeta_boxed_1290_; lean_object* v_res_1291_; 
v_isMeta_boxed_1290_ = lean_unbox(v_isMeta_1289_);
v_res_1291_ = l_Lean_recordExtraModUse___redArg(v_inst_1282_, v_inst_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_inst_1287_, v_modName_1288_, v_isMeta_boxed_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_modName_1299_, uint8_t v_isMeta_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_recordExtraModUse___redArg(v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_, v_inst_1298_, v_modName_1299_, v_isMeta_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_modName_1309_, lean_object* v_isMeta_1310_){
_start:
{
uint8_t v_isMeta_boxed_1311_; lean_object* v_res_1312_; 
v_isMeta_boxed_1311_ = lean_unbox(v_isMeta_1310_);
v_res_1312_ = l_Lean_recordExtraModUse(v_m_1302_, v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_, v_inst_1308_, v_modName_1309_, v_isMeta_boxed_1311_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1313_, lean_object* v_____s_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1317_, lean_object* v_toPure_1318_, lean_object* v_r_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1317_);
v___x_1321_ = lean_apply_2(v_toPure_1318_, lean_box(0), v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1322_, lean_object* v___x_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_declName_1330_, lean_object* v_toBind_1331_, lean_object* v___f_1332_, lean_object* v_a_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v_modules_1337_; lean_object* v___x_1338_; lean_object* v_toImport_1339_; lean_object* v_module_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1336_ = l_Lean_Environment_header(v_env_1322_);
v_modules_1337_ = lean_ctor_get(v___x_1336_, 3);
lean_inc_ref(v_modules_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = lean_array_get(v___x_1323_, v_modules_1337_, v_a_1333_);
lean_dec_ref(v_modules_1337_);
v_toImport_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc_ref(v_toImport_1339_);
lean_dec(v___x_1338_);
v_module_1340_ = lean_ctor_get(v_toImport_1339_, 0);
lean_inc(v_module_1340_);
lean_dec_ref(v_toImport_1339_);
v___x_1341_ = 0;
v___x_1342_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1324_, v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_module_1340_, v___x_1341_, v_declName_1330_);
v___x_1343_ = lean_apply_4(v_toBind_1331_, lean_box(0), lean_box(0), v___x_1342_, v___f_1332_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1344_, lean_object* v___x_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_declName_1352_, lean_object* v_toBind_1353_, lean_object* v___f_1354_, lean_object* v_a_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1344_, v___x_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_inst_1351_, v_declName_1352_, v_toBind_1353_, v___f_1354_, v_a_1355_, v_x_1356_, v___y_1357_);
lean_dec(v_a_1355_);
lean_dec_ref(v___x_1345_);
lean_dec_ref(v_env_1344_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1359_, lean_object* v_env_1360_, lean_object* v___x_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_declName_1368_, lean_object* v_toBind_1369_, lean_object* v___f_1370_, lean_object* v___x_1371_, lean_object* v___x_1372_, lean_object* v___x_1373_, lean_object* v_____r_1374_){
_start:
{
lean_object* v___y_1376_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1384_ = l_Lean_indirectModUseExt;
v___x_1385_ = lean_box(1);
v___x_1386_ = lean_box(0);
lean_inc_ref(v_env_1360_);
v___x_1387_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1371_, v___x_1384_, v_env_1360_, v___x_1385_, v___x_1386_);
lean_inc(v_declName_1368_);
v___x_1388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1372_, v___x_1373_, v___x_1387_, v_declName_1368_);
lean_dec(v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1376_ = v___x_1389_;
goto v___jp_1375_;
}
else
{
lean_object* v_val_1390_; 
v_val_1390_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1388_, 1);
v___y_1376_ = v_val_1390_;
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; size_t v_sz_1380_; size_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1377_ = lean_box(0);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1378_, 0, v___x_1377_);
lean_closure_set(v___f_1378_, 1, v_toPure_1359_);
lean_inc(v_toBind_1369_);
lean_inc_ref(v_inst_1362_);
v___f_1379_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1379_, 0, v_env_1360_);
lean_closure_set(v___f_1379_, 1, v___x_1361_);
lean_closure_set(v___f_1379_, 2, v_inst_1362_);
lean_closure_set(v___f_1379_, 3, v_inst_1363_);
lean_closure_set(v___f_1379_, 4, v_inst_1364_);
lean_closure_set(v___f_1379_, 5, v_inst_1365_);
lean_closure_set(v___f_1379_, 6, v_inst_1366_);
lean_closure_set(v___f_1379_, 7, v_inst_1367_);
lean_closure_set(v___f_1379_, 8, v_declName_1368_);
lean_closure_set(v___f_1379_, 9, v_toBind_1369_);
lean_closure_set(v___f_1379_, 10, v___f_1378_);
v_sz_1380_ = lean_array_size(v___y_1376_);
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1362_, v___y_1376_, v___f_1379_, v_sz_1380_, v___x_1381_, v___x_1377_);
v___x_1383_ = lean_apply_4(v_toBind_1369_, lean_box(0), lean_box(0), v___x_1382_, v___f_1370_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_declName_1398_, lean_object* v_toBind_1399_, lean_object* v___f_1400_, uint8_t v_isMeta_1401_, lean_object* v_____do__lift_1402_){
_start:
{
uint8_t v___y_1404_; 
if (v_isMeta_1401_ == 0)
{
lean_dec_ref(v_____do__lift_1402_);
v___y_1404_ = v_isMeta_1401_;
goto v___jp_1403_;
}
else
{
uint8_t v___x_1409_; 
lean_inc(v_declName_1398_);
v___x_1409_ = l_Lean_isMarkedMeta(v_____do__lift_1402_, v_declName_1398_);
if (v___x_1409_ == 0)
{
v___y_1404_ = v_isMeta_1401_;
goto v___jp_1403_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = 0;
v___y_1404_ = v___x_1410_;
goto v___jp_1403_;
}
}
v___jp_1403_:
{
lean_object* v_toImport_1405_; lean_object* v_module_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_toImport_1405_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_toImport_1405_);
lean_dec_ref(v___x_1391_);
v_module_1406_ = lean_ctor_get(v_toImport_1405_, 0);
lean_inc(v_module_1406_);
lean_dec_ref(v_toImport_1405_);
v___x_1407_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1392_, v_inst_1393_, v_inst_1394_, v_inst_1395_, v_inst_1396_, v_inst_1397_, v_module_1406_, v___y_1404_, v_declName_1398_);
v___x_1408_ = lean_apply_4(v_toBind_1399_, lean_box(0), lean_box(0), v___x_1407_, v___f_1400_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_declName_1418_, lean_object* v_toBind_1419_, lean_object* v___f_1420_, lean_object* v_isMeta_1421_, lean_object* v_____do__lift_1422_){
_start:
{
uint8_t v_isMeta_boxed_1423_; lean_object* v_res_1424_; 
v_isMeta_boxed_1423_ = lean_unbox(v_isMeta_1421_);
v_res_1424_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1411_, v_inst_1412_, v_inst_1413_, v_inst_1414_, v_inst_1415_, v_inst_1416_, v_inst_1417_, v_declName_1418_, v_toBind_1419_, v___f_1420_, v_isMeta_boxed_1423_, v_____do__lift_1422_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1425_, lean_object* v_declName_1426_, lean_object* v___x_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_toBind_1434_, lean_object* v___f_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, lean_object* v___x_1438_, uint8_t v_isMeta_1439_, lean_object* v_getEnv_1440_, lean_object* v_env_1441_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1441_, v_declName_1426_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_dec_ref(v_env_1441_);
lean_dec(v_getEnv_1440_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec(v___f_1435_);
lean_dec(v_toBind_1434_);
lean_dec(v_inst_1433_);
lean_dec_ref(v_inst_1432_);
lean_dec(v_inst_1431_);
lean_dec_ref(v_inst_1430_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec_ref(v___x_1427_);
lean_dec(v_declName_1426_);
goto v___jp_1442_;
}
else
{
lean_object* v_val_1446_; lean_object* v___x_1447_; lean_object* v_modules_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_val_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_val_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = l_Lean_Environment_header(v_env_1441_);
v_modules_1448_ = lean_ctor_get(v___x_1447_, 3);
lean_inc_ref(v_modules_1448_);
lean_dec_ref(v___x_1447_);
v___x_1449_ = lean_array_get_size(v_modules_1448_);
v___x_1450_ = lean_nat_dec_lt(v_val_1446_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_dec_ref(v_modules_1448_);
lean_dec(v_val_1446_);
lean_dec_ref(v_env_1441_);
lean_dec(v_getEnv_1440_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec(v___f_1435_);
lean_dec(v_toBind_1434_);
lean_dec(v_inst_1433_);
lean_dec_ref(v_inst_1432_);
lean_dec(v_inst_1431_);
lean_dec_ref(v_inst_1430_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec_ref(v___x_1427_);
lean_dec(v_declName_1426_);
goto v___jp_1442_;
}
else
{
lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___f_1454_; lean_object* v___x_1455_; 
lean_inc_n(v_toBind_1434_, 2);
lean_inc(v_declName_1426_);
lean_inc(v_inst_1433_);
lean_inc_ref(v_inst_1432_);
lean_inc(v_inst_1431_);
lean_inc_ref(v_inst_1430_);
lean_inc_ref(v_inst_1429_);
lean_inc_ref(v_inst_1428_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1451_, 0, v_toPure_1425_);
lean_closure_set(v___f_1451_, 1, v_env_1441_);
lean_closure_set(v___f_1451_, 2, v___x_1427_);
lean_closure_set(v___f_1451_, 3, v_inst_1428_);
lean_closure_set(v___f_1451_, 4, v_inst_1429_);
lean_closure_set(v___f_1451_, 5, v_inst_1430_);
lean_closure_set(v___f_1451_, 6, v_inst_1431_);
lean_closure_set(v___f_1451_, 7, v_inst_1432_);
lean_closure_set(v___f_1451_, 8, v_inst_1433_);
lean_closure_set(v___f_1451_, 9, v_declName_1426_);
lean_closure_set(v___f_1451_, 10, v_toBind_1434_);
lean_closure_set(v___f_1451_, 11, v___f_1435_);
lean_closure_set(v___f_1451_, 12, v___x_1436_);
lean_closure_set(v___f_1451_, 13, v___x_1437_);
lean_closure_set(v___f_1451_, 14, v___x_1438_);
v___x_1452_ = lean_array_fget(v_modules_1448_, v_val_1446_);
lean_dec(v_val_1446_);
lean_dec_ref(v_modules_1448_);
v___x_1453_ = lean_box(v_isMeta_1439_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1454_, 0, v___x_1452_);
lean_closure_set(v___f_1454_, 1, v_inst_1428_);
lean_closure_set(v___f_1454_, 2, v_inst_1429_);
lean_closure_set(v___f_1454_, 3, v_inst_1430_);
lean_closure_set(v___f_1454_, 4, v_inst_1431_);
lean_closure_set(v___f_1454_, 5, v_inst_1432_);
lean_closure_set(v___f_1454_, 6, v_inst_1433_);
lean_closure_set(v___f_1454_, 7, v_declName_1426_);
lean_closure_set(v___f_1454_, 8, v_toBind_1434_);
lean_closure_set(v___f_1454_, 9, v___f_1451_);
lean_closure_set(v___f_1454_, 10, v___x_1453_);
v___x_1455_ = lean_apply_4(v_toBind_1434_, lean_box(0), lean_box(0), v_getEnv_1440_, v___f_1454_);
return v___x_1455_;
}
}
v___jp_1442_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_apply_2(v_toPure_1425_, lean_box(0), v___x_1443_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1456_ = _args[0];
lean_object* v_declName_1457_ = _args[1];
lean_object* v___x_1458_ = _args[2];
lean_object* v_inst_1459_ = _args[3];
lean_object* v_inst_1460_ = _args[4];
lean_object* v_inst_1461_ = _args[5];
lean_object* v_inst_1462_ = _args[6];
lean_object* v_inst_1463_ = _args[7];
lean_object* v_inst_1464_ = _args[8];
lean_object* v_toBind_1465_ = _args[9];
lean_object* v___f_1466_ = _args[10];
lean_object* v___x_1467_ = _args[11];
lean_object* v___x_1468_ = _args[12];
lean_object* v___x_1469_ = _args[13];
lean_object* v_isMeta_1470_ = _args[14];
lean_object* v_getEnv_1471_ = _args[15];
lean_object* v_env_1472_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1473_; lean_object* v_res_1474_; 
v_isMeta_boxed_1473_ = lean_unbox(v_isMeta_1470_);
v_res_1474_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1456_, v_declName_1457_, v___x_1458_, v_inst_1459_, v_inst_1460_, v_inst_1461_, v_inst_1462_, v_inst_1463_, v_inst_1464_, v_toBind_1465_, v___f_1466_, v___x_1467_, v___x_1468_, v___x_1469_, v_isMeta_boxed_1473_, v_getEnv_1471_, v_env_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_declName_1481_, uint8_t v_isMeta_1482_){
_start:
{
lean_object* v_toApplicative_1483_; lean_object* v_toBind_1484_; lean_object* v_getEnv_1485_; lean_object* v_toPure_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___x_1494_; 
v_toApplicative_1483_ = lean_ctor_get(v_inst_1475_, 0);
v_toBind_1484_ = lean_ctor_get(v_inst_1475_, 1);
lean_inc_n(v_toBind_1484_, 2);
v_getEnv_1485_ = lean_ctor_get(v_inst_1476_, 0);
lean_inc_n(v_getEnv_1485_, 2);
v_toPure_1486_ = lean_ctor_get(v_toApplicative_1483_, 1);
lean_inc_n(v_toPure_1486_, 2);
v___x_1487_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__0));
v___x_1488_ = ((lean_object*)(l_Lean_getIndirectModUses___closed__1));
v___x_1489_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__2, &l_Lean_getIndirectModUses___closed__2_once, _init_l_Lean_getIndirectModUses___closed__2);
v___x_1490_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1491_, 0, v_toPure_1486_);
v___x_1492_ = lean_box(v_isMeta_1482_);
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1493_, 0, v_toPure_1486_);
lean_closure_set(v___f_1493_, 1, v_declName_1481_);
lean_closure_set(v___f_1493_, 2, v___x_1490_);
lean_closure_set(v___f_1493_, 3, v_inst_1475_);
lean_closure_set(v___f_1493_, 4, v_inst_1476_);
lean_closure_set(v___f_1493_, 5, v_inst_1477_);
lean_closure_set(v___f_1493_, 6, v_inst_1478_);
lean_closure_set(v___f_1493_, 7, v_inst_1479_);
lean_closure_set(v___f_1493_, 8, v_inst_1480_);
lean_closure_set(v___f_1493_, 9, v_toBind_1484_);
lean_closure_set(v___f_1493_, 10, v___f_1491_);
lean_closure_set(v___f_1493_, 11, v___x_1489_);
lean_closure_set(v___f_1493_, 12, v___x_1487_);
lean_closure_set(v___f_1493_, 13, v___x_1488_);
lean_closure_set(v___f_1493_, 14, v___x_1492_);
lean_closure_set(v___f_1493_, 15, v_getEnv_1485_);
v___x_1494_ = lean_apply_4(v_toBind_1484_, lean_box(0), lean_box(0), v_getEnv_1485_, v___f_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_declName_1501_, lean_object* v_isMeta_1502_){
_start:
{
uint8_t v_isMeta_boxed_1503_; lean_object* v_res_1504_; 
v_isMeta_boxed_1503_ = lean_unbox(v_isMeta_1502_);
v_res_1504_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1495_, v_inst_1496_, v_inst_1497_, v_inst_1498_, v_inst_1499_, v_inst_1500_, v_declName_1501_, v_isMeta_boxed_1503_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_declName_1512_, uint8_t v_isMeta_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_declName_1512_, v_isMeta_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_declName_1522_, lean_object* v_isMeta_1523_){
_start:
{
uint8_t v_isMeta_boxed_1524_; lean_object* v_res_1525_; 
v_isMeta_boxed_1524_ = lean_unbox(v_isMeta_1523_);
v_res_1525_ = l_Lean_recordExtraModUseFromDecl(v_m_1515_, v_inst_1516_, v_inst_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_declName_1522_, v_isMeta_boxed_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1526_, lean_object* v_e_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_box(0);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1531_);
lean_dec_ref(v_x_1531_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_array_mk(v_es_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1551_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1553_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1557_, lean_object* v_modIdx_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1559_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1560_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1561_ = 0;
v___x_1562_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1559_, v___x_1560_, v_env_1557_, v_modIdx_1558_, v___x_1561_);
v___x_1563_ = lean_array_get_size(v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_nat_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; 
v___x_1566_ = 1;
return v___x_1566_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = 0;
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1568_, lean_object* v_modIdx_1569_){
_start:
{
uint8_t v_res_1570_; lean_object* v_r_1571_; 
v_res_1570_ = l_Lean_isExtraRevModUse(v_env_1568_, v_modIdx_1569_);
lean_dec(v_modIdx_1569_);
lean_dec_ref(v_env_1568_);
v_r_1571_ = lean_box(v_res_1570_);
return v_r_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v_toEnvExtension_1574_; lean_object* v_asyncMode_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_toEnvExtension_1574_ = lean_ctor_get(v___x_1572_, 0);
v_asyncMode_1575_ = lean_ctor_get(v_toEnvExtension_1574_, 2);
lean_inc(v_asyncMode_1575_);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_box(0);
v___x_1578_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1572_, v_x_1573_, v___x_1576_, v_asyncMode_1575_, v___x_1577_);
lean_dec(v_asyncMode_1575_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v_modifyEnv_1582_, lean_object* v___f_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_cls_1588_, lean_object* v_toBind_1589_, lean_object* v___f_1590_, uint8_t v_____do__lift_1591_){
_start:
{
if (v_____do__lift_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_dec(v___f_1590_);
lean_dec(v_toBind_1589_);
lean_dec(v_cls_1588_);
lean_dec(v_inst_1587_);
lean_dec_ref(v_inst_1586_);
lean_dec_ref(v_inst_1585_);
lean_dec_ref(v_inst_1584_);
v___x_1592_ = lean_apply_1(v_modifyEnv_1582_, v___f_1583_);
return v___x_1592_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___f_1583_);
lean_dec(v_modifyEnv_1582_);
v___x_1593_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1);
v___x_1594_ = l_Lean_addTrace___redArg(v_inst_1584_, v_inst_1585_, v_inst_1586_, v_inst_1587_, v_cls_1588_, v___x_1593_);
v___x_1595_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1594_, v___f_1590_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___boxed(lean_object* v_modifyEnv_1596_, lean_object* v___f_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_cls_1602_, lean_object* v_toBind_1603_, lean_object* v___f_1604_, lean_object* v_____do__lift_1605_){
_start:
{
uint8_t v_____do__lift_184__boxed_1606_; lean_object* v_res_1607_; 
v_____do__lift_184__boxed_1606_ = lean_unbox(v_____do__lift_1605_);
v_res_1607_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(v_modifyEnv_1596_, v___f_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v_cls_1602_, v_toBind_1603_, v___f_1604_, v_____do__lift_184__boxed_1606_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___f_1609_; 
v___x_1608_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1609_, 0, v___x_1608_);
return v___f_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object* v___x_1610_, lean_object* v_toPure_1611_, lean_object* v_inst_1612_, lean_object* v_modifyEnv_1613_, lean_object* v_toBind_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_____do__lift_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1620_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1621_ = lean_box(1);
v___x_1622_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1610_, v___x_1620_, v_____do__lift_1619_, v___x_1621_);
v___x_1623_ = l_List_isEmpty___redArg(v___x_1622_);
lean_dec(v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v_inst_1618_);
lean_dec_ref(v_inst_1617_);
lean_dec_ref(v_inst_1616_);
lean_dec(v_inst_1615_);
lean_dec(v_toBind_1614_);
lean_dec(v_modifyEnv_1613_);
lean_dec_ref(v_inst_1612_);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_apply_2(v_toPure_1611_, lean_box(0), v___x_1624_);
return v___x_1625_;
}
else
{
lean_object* v_getInheritedTraceOptions_1626_; lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v_cls_1629_; lean_object* v___f_1630_; lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_getInheritedTraceOptions_1626_ = lean_ctor_get(v_inst_1612_, 2);
lean_inc(v_getInheritedTraceOptions_1626_);
v___f_1627_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0);
lean_inc(v_modifyEnv_1613_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1628_, 0, v_modifyEnv_1613_);
lean_closure_set(v___f_1628_, 1, v___f_1627_);
v_cls_1629_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1614_, 3);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1630_, 0, v_toPure_1611_);
lean_closure_set(v___f_1630_, 1, v_cls_1629_);
lean_closure_set(v___f_1630_, 2, v_toBind_1614_);
lean_closure_set(v___f_1630_, 3, v_inst_1615_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1631_, 0, v_modifyEnv_1613_);
lean_closure_set(v___f_1631_, 1, v___f_1627_);
lean_closure_set(v___f_1631_, 2, v_inst_1616_);
lean_closure_set(v___f_1631_, 3, v_inst_1612_);
lean_closure_set(v___f_1631_, 4, v_inst_1617_);
lean_closure_set(v___f_1631_, 5, v_inst_1618_);
lean_closure_set(v___f_1631_, 6, v_cls_1629_);
lean_closure_set(v___f_1631_, 7, v_toBind_1614_);
lean_closure_set(v___f_1631_, 8, v___f_1628_);
v___x_1632_ = lean_apply_4(v_toBind_1614_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1626_, v___f_1630_);
v___x_1633_ = lean_apply_4(v_toBind_1614_, lean_box(0), lean_box(0), v___x_1632_, v___f_1631_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_){
_start:
{
lean_object* v_toApplicative_1640_; lean_object* v_toBind_1641_; lean_object* v_getEnv_1642_; lean_object* v_modifyEnv_1643_; lean_object* v_toPure_1644_; lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; 
v_toApplicative_1640_ = lean_ctor_get(v_inst_1634_, 0);
v_toBind_1641_ = lean_ctor_get(v_inst_1634_, 1);
lean_inc_n(v_toBind_1641_, 2);
v_getEnv_1642_ = lean_ctor_get(v_inst_1635_, 0);
lean_inc(v_getEnv_1642_);
v_modifyEnv_1643_ = lean_ctor_get(v_inst_1635_, 1);
lean_inc(v_modifyEnv_1643_);
lean_dec_ref(v_inst_1635_);
v_toPure_1644_ = lean_ctor_get(v_toApplicative_1640_, 1);
lean_inc(v_toPure_1644_);
v___x_1645_ = lean_box(0);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1646_, 0, v___x_1645_);
lean_closure_set(v___f_1646_, 1, v_toPure_1644_);
lean_closure_set(v___f_1646_, 2, v_inst_1636_);
lean_closure_set(v___f_1646_, 3, v_modifyEnv_1643_);
lean_closure_set(v___f_1646_, 4, v_toBind_1641_);
lean_closure_set(v___f_1646_, 5, v_inst_1637_);
lean_closure_set(v___f_1646_, 6, v_inst_1634_);
lean_closure_set(v___f_1646_, 7, v_inst_1638_);
lean_closure_set(v___f_1646_, 8, v_inst_1639_);
v___x_1647_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v_getEnv_1642_, v___f_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1649_, v_inst_1650_, v_inst_1651_, v_inst_1652_, v_inst_1653_, v_inst_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(4259277863u);
v___x_1671_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1672_ = l_Lean_Name_num___override(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1675_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1676_ = l_Lean_Name_str___override(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1679_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1680_ = l_Lean_Name_str___override(v___x_1679_, v___x_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(2u);
v___x_1682_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1683_ = l_Lean_Name_num___override(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1686_ = 0;
v___x_1687_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1688_ = l_Lean_registerTraceClass(v___x_1685_, v___x_1686_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1690_;
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
