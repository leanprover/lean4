// Lean compiler output
// Module: Lean.Compiler.Bytecode.Instruction
// Imports: public import Lean.Compiler.Bytecode.Basic import Init.Omega
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
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_int32_add(uint32_t, uint32_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_replicateTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint32_land(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_BitVec_toHex(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_instInhabitedInstruction_default;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_instInhabitedInstruction;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_maxUConst;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_maxNConst;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uconst(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uconst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_nconst(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_nconst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_move(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_move___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_ret(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ret___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_call(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_call___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_retcall(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_retcall___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_computeScalar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_computeScalar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_allocCtor(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_allocCtor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_proj(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_proj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uproj(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uproj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj8(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj16(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj16___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_set(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uset(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uset___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset8(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset16(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset16___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxSmall(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxSmall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUSize(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxSmall(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxSmall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUSize(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_inc(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_inc___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_dec(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_dec___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_isShared(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_isShared___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_loadTag(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_jumpTable(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jumpTable___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_setTag(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_setTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_loadConst(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadConst___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_ifTag(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ifTag___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_jump___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Compiler_Bytecode_Instruction_jump___closed__0;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_jump(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jump___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_nojump;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_app(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_app___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_pap(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_pap___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_del(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_del___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_reset(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reset___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_reuse(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reuse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_storeCache(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_storeCache___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_skipIfCached(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_skipIfCached___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_declConst(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_declConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_assemblerInternal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_addrToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0x"};
static const lean_object* l_Lean_Compiler_Bytecode_addrToString___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_addrToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_Bytecode_Instruction_toString_spec__0(lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decl_const R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__0_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " @"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__1 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__1_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "skip_if_cached "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__2 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__2_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "store_cache R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__3 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__3_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reuse R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__4 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__4_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__5 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__5_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reset "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__6 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__6_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__7 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__7_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "del R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__8 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__8_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pap "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__9 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__9_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__10 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__10_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "app "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__11 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__11_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "jump "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__12 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_toString___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__13;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "if_tag R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__14 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_toString___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__15;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "load_const #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__16 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__16_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "set_tag R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__17 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__17_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "table R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__18 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__18_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "load_tag R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__19 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__19_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "is_shared R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__20 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__20_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dec R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__21 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__21_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "inc R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__22 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__22_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unbox_f32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__23 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__23_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unbox_f64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__24 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__24_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unbox_usz R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__25 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__25_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unbox64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__26 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__26_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unbox32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__27 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__27_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unbox R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__28 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__28_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "box_f32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__29 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__29_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "box_f64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__30 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__30_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "box_usz R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__31 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__31_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "box64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__32 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__32_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "box32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__33 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__33_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "box R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__34 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__34_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sset64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__35 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__35_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sset32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__36 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__36_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sset16 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__37 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__37_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sset8 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__38 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__38_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "uset R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__39 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__39_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "set R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__40 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__40_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sproj64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__41 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__41_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sproj32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__42 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__42_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sproj16 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__43 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__43_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sproj8 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__44 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__44_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "uproj R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__45 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__45_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proj R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__46 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__46_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ctor R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__47 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__47_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scalar "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__48 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__48_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "retcall #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__49 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__49_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "call #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__50 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__50_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ret R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__51 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__51_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "move R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__52 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__52_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "uconst R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__53 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__53_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Declaration "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__0_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " (arity "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__1 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__1_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ") with "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__2 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__2_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " stack and "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__3 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__3_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " reserved\n"};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__4 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__4_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Code:\n"};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__5 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__5_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Symbol table:\n"};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__6 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__6_value;
LEAN_EXPORT lean_object* lean_bytecode_disass(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction_default(void){
_start:
{
uint32_t v___x_1_; 
v___x_1_ = 0;
return v___x_1_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction(void){
_start:
{
uint32_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_maxUConst(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(262143u);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_maxNConst(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(131071u);
return v___x_4_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_uconst(uint32_t v_target_5_, uint32_t v_val_6_){
_start:
{
uint32_t v___x_7_; uint32_t v___x_8_; uint32_t v___x_9_; 
v___x_7_ = 18;
v___x_8_ = lean_uint32_shift_left(v_target_5_, v___x_7_);
v___x_9_ = lean_uint32_lor(v___x_8_, v_val_6_);
return v___x_9_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_uconst_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_5_ = stack[0].m_num;
uint32_t v_val_6_ = stack[1].m_num;
uint32_t v_res_10_;
v_res_10_ = l_Lean_Compiler_Bytecode_Instruction_uconst(v_target_5_, v_val_6_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uconst___boxed(lean_object* v_target_11_, lean_object* v_val_12_){
_start:
{
uint32_t v_target_boxed_13_; uint32_t v_val_boxed_14_; uint32_t v_res_15_; lean_object* v_r_16_; 
v_target_boxed_13_ = lean_unbox_uint32(v_target_11_);
lean_dec(v_target_11_);
v_val_boxed_14_ = lean_unbox_uint32(v_val_12_);
lean_dec(v_val_12_);
v_res_15_ = l_Lean_Compiler_Bytecode_Instruction_uconst(v_target_boxed_13_, v_val_boxed_14_);
v_r_16_ = lean_box_uint32(v_res_15_);
return v_r_16_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_nconst(uint32_t v_target_17_, uint32_t v_val_18_){
_start:
{
uint32_t v___x_19_; uint32_t v___x_20_; uint32_t v___x_21_; uint32_t v___x_22_; 
v___x_19_ = 1;
v___x_20_ = lean_uint32_shift_left(v_val_18_, v___x_19_);
v___x_21_ = lean_uint32_lor(v___x_20_, v___x_19_);
v___x_22_ = l_Lean_Compiler_Bytecode_Instruction_uconst(v_target_17_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_nconst_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_17_ = stack[0].m_num;
uint32_t v_val_18_ = stack[1].m_num;
uint32_t v_res_23_;
v_res_23_ = l_Lean_Compiler_Bytecode_Instruction_nconst(v_target_17_, v_val_18_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_nconst___boxed(lean_object* v_target_24_, lean_object* v_val_25_){
_start:
{
uint32_t v_target_boxed_26_; uint32_t v_val_boxed_27_; uint32_t v_res_28_; lean_object* v_r_29_; 
v_target_boxed_26_ = lean_unbox_uint32(v_target_24_);
lean_dec(v_target_24_);
v_val_boxed_27_ = lean_unbox_uint32(v_val_25_);
lean_dec(v_val_25_);
v_res_28_ = l_Lean_Compiler_Bytecode_Instruction_nconst(v_target_boxed_26_, v_val_boxed_27_);
v_r_29_ = lean_box_uint32(v_res_28_);
return v_r_29_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_move(uint32_t v_target_30_, uint32_t v_source_31_){
_start:
{
uint32_t v___x_32_; uint32_t v___x_33_; uint32_t v___x_34_; uint32_t v___x_35_; uint32_t v___x_36_; 
v___x_32_ = 67108864;
v___x_33_ = 13;
v___x_34_ = lean_uint32_shift_left(v_target_30_, v___x_33_);
v___x_35_ = lean_uint32_lor(v___x_32_, v___x_34_);
v___x_36_ = lean_uint32_lor(v___x_35_, v_source_31_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_move_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_30_ = stack[0].m_num;
uint32_t v_source_31_ = stack[1].m_num;
uint32_t v_res_37_;
v_res_37_ = l_Lean_Compiler_Bytecode_Instruction_move(v_target_30_, v_source_31_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_move___boxed(lean_object* v_target_38_, lean_object* v_source_39_){
_start:
{
uint32_t v_target_boxed_40_; uint32_t v_source_boxed_41_; uint32_t v_res_42_; lean_object* v_r_43_; 
v_target_boxed_40_ = lean_unbox_uint32(v_target_38_);
lean_dec(v_target_38_);
v_source_boxed_41_ = lean_unbox_uint32(v_source_39_);
lean_dec(v_source_39_);
v_res_42_ = l_Lean_Compiler_Bytecode_Instruction_move(v_target_boxed_40_, v_source_boxed_41_);
v_r_43_ = lean_box_uint32(v_res_42_);
return v_r_43_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_ret(uint32_t v_target_44_){
_start:
{
uint32_t v___x_45_; uint32_t v___x_46_; 
v___x_45_ = 134217728;
v___x_46_ = lean_uint32_lor(v___x_45_, v_target_44_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_ret_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_44_ = stack[0].m_num;
uint32_t v_res_47_;
v_res_47_ = l_Lean_Compiler_Bytecode_Instruction_ret(v_target_44_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ret___boxed(lean_object* v_target_48_){
_start:
{
uint32_t v_target_boxed_49_; uint32_t v_res_50_; lean_object* v_r_51_; 
v_target_boxed_49_ = lean_unbox_uint32(v_target_48_);
lean_dec(v_target_48_);
v_res_50_ = l_Lean_Compiler_Bytecode_Instruction_ret(v_target_boxed_49_);
v_r_51_ = lean_box_uint32(v_res_50_);
return v_r_51_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_call(uint32_t v_fn_52_){
_start:
{
uint32_t v___x_53_; uint32_t v___x_54_; 
v___x_53_ = 201326592;
v___x_54_ = lean_uint32_lor(v___x_53_, v_fn_52_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_call_0interp(lean_interpreter_value* stack)
{
uint32_t v_fn_52_ = stack[0].m_num;
uint32_t v_res_55_;
v_res_55_ = l_Lean_Compiler_Bytecode_Instruction_call(v_fn_52_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_call___boxed(lean_object* v_fn_56_){
_start:
{
uint32_t v_fn_boxed_57_; uint32_t v_res_58_; lean_object* v_r_59_; 
v_fn_boxed_57_ = lean_unbox_uint32(v_fn_56_);
lean_dec(v_fn_56_);
v_res_58_ = l_Lean_Compiler_Bytecode_Instruction_call(v_fn_boxed_57_);
v_r_59_ = lean_box_uint32(v_res_58_);
return v_r_59_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_retcall(uint32_t v_fn_60_){
_start:
{
uint32_t v___x_61_; uint32_t v___x_62_; 
v___x_61_ = 268435456;
v___x_62_ = lean_uint32_lor(v___x_61_, v_fn_60_);
return v___x_62_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_retcall_0interp(lean_interpreter_value* stack)
{
uint32_t v_fn_60_ = stack[0].m_num;
uint32_t v_res_63_;
v_res_63_ = l_Lean_Compiler_Bytecode_Instruction_retcall(v_fn_60_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_retcall___boxed(lean_object* v_fn_64_){
_start:
{
uint32_t v_fn_boxed_65_; uint32_t v_res_66_; lean_object* v_r_67_; 
v_fn_boxed_65_ = lean_unbox_uint32(v_fn_64_);
lean_dec(v_fn_64_);
v_res_66_ = l_Lean_Compiler_Bytecode_Instruction_retcall(v_fn_boxed_65_);
v_r_67_ = lean_box_uint32(v_res_66_);
return v_r_67_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_computeScalar(uint32_t v_usize_68_, uint32_t v_ssize_69_){
_start:
{
uint32_t v___x_70_; uint32_t v___x_71_; uint32_t v___x_72_; uint32_t v___x_73_; uint32_t v___x_74_; 
v___x_70_ = 335544320;
v___x_71_ = 13;
v___x_72_ = lean_uint32_shift_left(v_usize_68_, v___x_71_);
v___x_73_ = lean_uint32_lor(v___x_70_, v___x_72_);
v___x_74_ = lean_uint32_lor(v___x_73_, v_ssize_69_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_computeScalar_0interp(lean_interpreter_value* stack)
{
uint32_t v_usize_68_ = stack[0].m_num;
uint32_t v_ssize_69_ = stack[1].m_num;
uint32_t v_res_75_;
v_res_75_ = l_Lean_Compiler_Bytecode_Instruction_computeScalar(v_usize_68_, v_ssize_69_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_computeScalar___boxed(lean_object* v_usize_76_, lean_object* v_ssize_77_){
_start:
{
uint32_t v_usize_boxed_78_; uint32_t v_ssize_boxed_79_; uint32_t v_res_80_; lean_object* v_r_81_; 
v_usize_boxed_78_ = lean_unbox_uint32(v_usize_76_);
lean_dec(v_usize_76_);
v_ssize_boxed_79_ = lean_unbox_uint32(v_ssize_77_);
lean_dec(v_ssize_77_);
v_res_80_ = l_Lean_Compiler_Bytecode_Instruction_computeScalar(v_usize_boxed_78_, v_ssize_boxed_79_);
v_r_81_ = lean_box_uint32(v_res_80_);
return v_r_81_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_allocCtor(uint32_t v_target_82_, uint32_t v_tag_83_, uint32_t v_numObjs_84_){
_start:
{
uint32_t v___x_85_; uint32_t v___x_86_; uint32_t v___x_87_; uint32_t v___x_88_; uint32_t v___x_89_; uint32_t v___x_90_; uint32_t v___x_91_; uint32_t v___x_92_; 
v___x_85_ = 402653184;
v___x_86_ = 18;
v___x_87_ = lean_uint32_shift_left(v_target_82_, v___x_86_);
v___x_88_ = lean_uint32_lor(v___x_85_, v___x_87_);
v___x_89_ = 8;
v___x_90_ = lean_uint32_shift_left(v_tag_83_, v___x_89_);
v___x_91_ = lean_uint32_lor(v___x_88_, v___x_90_);
v___x_92_ = lean_uint32_lor(v___x_91_, v_numObjs_84_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_allocCtor_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_82_ = stack[0].m_num;
uint32_t v_tag_83_ = stack[1].m_num;
uint32_t v_numObjs_84_ = stack[2].m_num;
uint32_t v_res_93_;
v_res_93_ = l_Lean_Compiler_Bytecode_Instruction_allocCtor(v_target_82_, v_tag_83_, v_numObjs_84_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_allocCtor___boxed(lean_object* v_target_94_, lean_object* v_tag_95_, lean_object* v_numObjs_96_){
_start:
{
uint32_t v_target_boxed_97_; uint32_t v_tag_boxed_98_; uint32_t v_numObjs_boxed_99_; uint32_t v_res_100_; lean_object* v_r_101_; 
v_target_boxed_97_ = lean_unbox_uint32(v_target_94_);
lean_dec(v_target_94_);
v_tag_boxed_98_ = lean_unbox_uint32(v_tag_95_);
lean_dec(v_tag_95_);
v_numObjs_boxed_99_ = lean_unbox_uint32(v_numObjs_96_);
lean_dec(v_numObjs_96_);
v_res_100_ = l_Lean_Compiler_Bytecode_Instruction_allocCtor(v_target_boxed_97_, v_tag_boxed_98_, v_numObjs_boxed_99_);
v_r_101_ = lean_box_uint32(v_res_100_);
return v_r_101_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_proj(uint32_t v_target_102_, uint32_t v_source_103_, uint32_t v_idx_104_){
_start:
{
uint32_t v___x_105_; uint32_t v___x_106_; uint32_t v___x_107_; uint32_t v___x_108_; uint32_t v___x_109_; uint32_t v___x_110_; uint32_t v___x_111_; uint32_t v___x_112_; 
v___x_105_ = 469762048;
v___x_106_ = 16;
v___x_107_ = lean_uint32_shift_left(v_target_102_, v___x_106_);
v___x_108_ = lean_uint32_lor(v___x_105_, v___x_107_);
v___x_109_ = 8;
v___x_110_ = lean_uint32_shift_left(v_source_103_, v___x_109_);
v___x_111_ = lean_uint32_lor(v___x_108_, v___x_110_);
v___x_112_ = lean_uint32_lor(v___x_111_, v_idx_104_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_proj_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_102_ = stack[0].m_num;
uint32_t v_source_103_ = stack[1].m_num;
uint32_t v_idx_104_ = stack[2].m_num;
uint32_t v_res_113_;
v_res_113_ = l_Lean_Compiler_Bytecode_Instruction_proj(v_target_102_, v_source_103_, v_idx_104_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_proj___boxed(lean_object* v_target_114_, lean_object* v_source_115_, lean_object* v_idx_116_){
_start:
{
uint32_t v_target_boxed_117_; uint32_t v_source_boxed_118_; uint32_t v_idx_boxed_119_; uint32_t v_res_120_; lean_object* v_r_121_; 
v_target_boxed_117_ = lean_unbox_uint32(v_target_114_);
lean_dec(v_target_114_);
v_source_boxed_118_ = lean_unbox_uint32(v_source_115_);
lean_dec(v_source_115_);
v_idx_boxed_119_ = lean_unbox_uint32(v_idx_116_);
lean_dec(v_idx_116_);
v_res_120_ = l_Lean_Compiler_Bytecode_Instruction_proj(v_target_boxed_117_, v_source_boxed_118_, v_idx_boxed_119_);
v_r_121_ = lean_box_uint32(v_res_120_);
return v_r_121_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_uproj(uint32_t v_target_122_, uint32_t v_source_123_, uint32_t v_idx_124_){
_start:
{
uint32_t v___x_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint32_t v___x_128_; uint32_t v___x_129_; uint32_t v___x_130_; uint32_t v___x_131_; uint32_t v___x_132_; 
v___x_125_ = 8;
v___x_126_ = 536870912;
v___x_127_ = 16;
v___x_128_ = lean_uint32_shift_left(v_target_122_, v___x_127_);
v___x_129_ = lean_uint32_lor(v___x_126_, v___x_128_);
v___x_130_ = lean_uint32_shift_left(v_source_123_, v___x_125_);
v___x_131_ = lean_uint32_lor(v___x_129_, v___x_130_);
v___x_132_ = lean_uint32_lor(v___x_131_, v_idx_124_);
return v___x_132_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_uproj_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_122_ = stack[0].m_num;
uint32_t v_source_123_ = stack[1].m_num;
uint32_t v_idx_124_ = stack[2].m_num;
uint32_t v_res_133_;
v_res_133_ = l_Lean_Compiler_Bytecode_Instruction_uproj(v_target_122_, v_source_123_, v_idx_124_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uproj___boxed(lean_object* v_target_134_, lean_object* v_source_135_, lean_object* v_idx_136_){
_start:
{
uint32_t v_target_boxed_137_; uint32_t v_source_boxed_138_; uint32_t v_idx_boxed_139_; uint32_t v_res_140_; lean_object* v_r_141_; 
v_target_boxed_137_ = lean_unbox_uint32(v_target_134_);
lean_dec(v_target_134_);
v_source_boxed_138_ = lean_unbox_uint32(v_source_135_);
lean_dec(v_source_135_);
v_idx_boxed_139_ = lean_unbox_uint32(v_idx_136_);
lean_dec(v_idx_136_);
v_res_140_ = l_Lean_Compiler_Bytecode_Instruction_uproj(v_target_boxed_137_, v_source_boxed_138_, v_idx_boxed_139_);
v_r_141_ = lean_box_uint32(v_res_140_);
return v_r_141_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj8(uint32_t v_target_142_, uint32_t v_source_143_){
_start:
{
uint32_t v___x_144_; uint32_t v___x_145_; uint32_t v___x_146_; uint32_t v___x_147_; uint32_t v___x_148_; 
v___x_144_ = 603979776;
v___x_145_ = 8;
v___x_146_ = lean_uint32_shift_left(v_target_142_, v___x_145_);
v___x_147_ = lean_uint32_lor(v___x_144_, v___x_146_);
v___x_148_ = lean_uint32_lor(v___x_147_, v_source_143_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sproj8_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_142_ = stack[0].m_num;
uint32_t v_source_143_ = stack[1].m_num;
uint32_t v_res_149_;
v_res_149_ = l_Lean_Compiler_Bytecode_Instruction_sproj8(v_target_142_, v_source_143_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj8___boxed(lean_object* v_target_150_, lean_object* v_source_151_){
_start:
{
uint32_t v_target_boxed_152_; uint32_t v_source_boxed_153_; uint32_t v_res_154_; lean_object* v_r_155_; 
v_target_boxed_152_ = lean_unbox_uint32(v_target_150_);
lean_dec(v_target_150_);
v_source_boxed_153_ = lean_unbox_uint32(v_source_151_);
lean_dec(v_source_151_);
v_res_154_ = l_Lean_Compiler_Bytecode_Instruction_sproj8(v_target_boxed_152_, v_source_boxed_153_);
v_r_155_ = lean_box_uint32(v_res_154_);
return v_r_155_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj16(uint32_t v_target_156_, uint32_t v_source_157_){
_start:
{
uint32_t v___x_158_; uint32_t v___x_159_; uint32_t v___x_160_; uint32_t v___x_161_; uint32_t v___x_162_; 
v___x_158_ = 671088640;
v___x_159_ = 8;
v___x_160_ = lean_uint32_shift_left(v_target_156_, v___x_159_);
v___x_161_ = lean_uint32_lor(v___x_158_, v___x_160_);
v___x_162_ = lean_uint32_lor(v___x_161_, v_source_157_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sproj16_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_156_ = stack[0].m_num;
uint32_t v_source_157_ = stack[1].m_num;
uint32_t v_res_163_;
v_res_163_ = l_Lean_Compiler_Bytecode_Instruction_sproj16(v_target_156_, v_source_157_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj16___boxed(lean_object* v_target_164_, lean_object* v_source_165_){
_start:
{
uint32_t v_target_boxed_166_; uint32_t v_source_boxed_167_; uint32_t v_res_168_; lean_object* v_r_169_; 
v_target_boxed_166_ = lean_unbox_uint32(v_target_164_);
lean_dec(v_target_164_);
v_source_boxed_167_ = lean_unbox_uint32(v_source_165_);
lean_dec(v_source_165_);
v_res_168_ = l_Lean_Compiler_Bytecode_Instruction_sproj16(v_target_boxed_166_, v_source_boxed_167_);
v_r_169_ = lean_box_uint32(v_res_168_);
return v_r_169_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj32(uint32_t v_target_170_, uint32_t v_source_171_){
_start:
{
uint32_t v___x_172_; uint32_t v___x_173_; uint32_t v___x_174_; uint32_t v___x_175_; uint32_t v___x_176_; 
v___x_172_ = 738197504;
v___x_173_ = 8;
v___x_174_ = lean_uint32_shift_left(v_target_170_, v___x_173_);
v___x_175_ = lean_uint32_lor(v___x_172_, v___x_174_);
v___x_176_ = lean_uint32_lor(v___x_175_, v_source_171_);
return v___x_176_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sproj32_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_170_ = stack[0].m_num;
uint32_t v_source_171_ = stack[1].m_num;
uint32_t v_res_177_;
v_res_177_ = l_Lean_Compiler_Bytecode_Instruction_sproj32(v_target_170_, v_source_171_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj32___boxed(lean_object* v_target_178_, lean_object* v_source_179_){
_start:
{
uint32_t v_target_boxed_180_; uint32_t v_source_boxed_181_; uint32_t v_res_182_; lean_object* v_r_183_; 
v_target_boxed_180_ = lean_unbox_uint32(v_target_178_);
lean_dec(v_target_178_);
v_source_boxed_181_ = lean_unbox_uint32(v_source_179_);
lean_dec(v_source_179_);
v_res_182_ = l_Lean_Compiler_Bytecode_Instruction_sproj32(v_target_boxed_180_, v_source_boxed_181_);
v_r_183_ = lean_box_uint32(v_res_182_);
return v_r_183_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj64(uint32_t v_target_184_, uint32_t v_source_185_){
_start:
{
uint32_t v___x_186_; uint32_t v___x_187_; uint32_t v___x_188_; uint32_t v___x_189_; uint32_t v___x_190_; 
v___x_186_ = 805306368;
v___x_187_ = 8;
v___x_188_ = lean_uint32_shift_left(v_target_184_, v___x_187_);
v___x_189_ = lean_uint32_lor(v___x_186_, v___x_188_);
v___x_190_ = lean_uint32_lor(v___x_189_, v_source_185_);
return v___x_190_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sproj64_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_184_ = stack[0].m_num;
uint32_t v_source_185_ = stack[1].m_num;
uint32_t v_res_191_;
v_res_191_ = l_Lean_Compiler_Bytecode_Instruction_sproj64(v_target_184_, v_source_185_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj64___boxed(lean_object* v_target_192_, lean_object* v_source_193_){
_start:
{
uint32_t v_target_boxed_194_; uint32_t v_source_boxed_195_; uint32_t v_res_196_; lean_object* v_r_197_; 
v_target_boxed_194_ = lean_unbox_uint32(v_target_192_);
lean_dec(v_target_192_);
v_source_boxed_195_ = lean_unbox_uint32(v_source_193_);
lean_dec(v_source_193_);
v_res_196_ = l_Lean_Compiler_Bytecode_Instruction_sproj64(v_target_boxed_194_, v_source_boxed_195_);
v_r_197_ = lean_box_uint32(v_res_196_);
return v_r_197_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_set(uint32_t v_target_198_, uint32_t v_source_199_, uint32_t v_idx_200_){
_start:
{
uint32_t v___x_201_; uint32_t v___x_202_; uint32_t v___x_203_; uint32_t v___x_204_; uint32_t v___x_205_; uint32_t v___x_206_; uint32_t v___x_207_; uint32_t v___x_208_; 
v___x_201_ = 872415232;
v___x_202_ = 16;
v___x_203_ = lean_uint32_shift_left(v_target_198_, v___x_202_);
v___x_204_ = lean_uint32_lor(v___x_201_, v___x_203_);
v___x_205_ = 8;
v___x_206_ = lean_uint32_shift_left(v_source_199_, v___x_205_);
v___x_207_ = lean_uint32_lor(v___x_204_, v___x_206_);
v___x_208_ = lean_uint32_lor(v___x_207_, v_idx_200_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_set_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_198_ = stack[0].m_num;
uint32_t v_source_199_ = stack[1].m_num;
uint32_t v_idx_200_ = stack[2].m_num;
uint32_t v_res_209_;
v_res_209_ = l_Lean_Compiler_Bytecode_Instruction_set(v_target_198_, v_source_199_, v_idx_200_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_set___boxed(lean_object* v_target_210_, lean_object* v_source_211_, lean_object* v_idx_212_){
_start:
{
uint32_t v_target_boxed_213_; uint32_t v_source_boxed_214_; uint32_t v_idx_boxed_215_; uint32_t v_res_216_; lean_object* v_r_217_; 
v_target_boxed_213_ = lean_unbox_uint32(v_target_210_);
lean_dec(v_target_210_);
v_source_boxed_214_ = lean_unbox_uint32(v_source_211_);
lean_dec(v_source_211_);
v_idx_boxed_215_ = lean_unbox_uint32(v_idx_212_);
lean_dec(v_idx_212_);
v_res_216_ = l_Lean_Compiler_Bytecode_Instruction_set(v_target_boxed_213_, v_source_boxed_214_, v_idx_boxed_215_);
v_r_217_ = lean_box_uint32(v_res_216_);
return v_r_217_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_uset(uint32_t v_target_218_, uint32_t v_source_219_, uint32_t v_idx_220_){
_start:
{
uint32_t v___x_221_; uint32_t v___x_222_; uint32_t v___x_223_; uint32_t v___x_224_; uint32_t v___x_225_; uint32_t v___x_226_; uint32_t v___x_227_; uint32_t v___x_228_; 
v___x_221_ = 939524096;
v___x_222_ = 16;
v___x_223_ = lean_uint32_shift_left(v_target_218_, v___x_222_);
v___x_224_ = lean_uint32_lor(v___x_221_, v___x_223_);
v___x_225_ = 8;
v___x_226_ = lean_uint32_shift_left(v_source_219_, v___x_225_);
v___x_227_ = lean_uint32_lor(v___x_224_, v___x_226_);
v___x_228_ = lean_uint32_lor(v___x_227_, v_idx_220_);
return v___x_228_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_uset_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_218_ = stack[0].m_num;
uint32_t v_source_219_ = stack[1].m_num;
uint32_t v_idx_220_ = stack[2].m_num;
uint32_t v_res_229_;
v_res_229_ = l_Lean_Compiler_Bytecode_Instruction_uset(v_target_218_, v_source_219_, v_idx_220_);
stack->m_num = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uset___boxed(lean_object* v_target_230_, lean_object* v_source_231_, lean_object* v_idx_232_){
_start:
{
uint32_t v_target_boxed_233_; uint32_t v_source_boxed_234_; uint32_t v_idx_boxed_235_; uint32_t v_res_236_; lean_object* v_r_237_; 
v_target_boxed_233_ = lean_unbox_uint32(v_target_230_);
lean_dec(v_target_230_);
v_source_boxed_234_ = lean_unbox_uint32(v_source_231_);
lean_dec(v_source_231_);
v_idx_boxed_235_ = lean_unbox_uint32(v_idx_232_);
lean_dec(v_idx_232_);
v_res_236_ = l_Lean_Compiler_Bytecode_Instruction_uset(v_target_boxed_233_, v_source_boxed_234_, v_idx_boxed_235_);
v_r_237_ = lean_box_uint32(v_res_236_);
return v_r_237_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sset8(uint32_t v_target_238_, uint32_t v_source_239_){
_start:
{
uint32_t v___x_240_; uint32_t v___x_241_; uint32_t v___x_242_; uint32_t v___x_243_; uint32_t v___x_244_; 
v___x_240_ = 1006632960;
v___x_241_ = 8;
v___x_242_ = lean_uint32_shift_left(v_target_238_, v___x_241_);
v___x_243_ = lean_uint32_lor(v___x_240_, v___x_242_);
v___x_244_ = lean_uint32_lor(v___x_243_, v_source_239_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sset8_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_238_ = stack[0].m_num;
uint32_t v_source_239_ = stack[1].m_num;
uint32_t v_res_245_;
v_res_245_ = l_Lean_Compiler_Bytecode_Instruction_sset8(v_target_238_, v_source_239_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset8___boxed(lean_object* v_target_246_, lean_object* v_source_247_){
_start:
{
uint32_t v_target_boxed_248_; uint32_t v_source_boxed_249_; uint32_t v_res_250_; lean_object* v_r_251_; 
v_target_boxed_248_ = lean_unbox_uint32(v_target_246_);
lean_dec(v_target_246_);
v_source_boxed_249_ = lean_unbox_uint32(v_source_247_);
lean_dec(v_source_247_);
v_res_250_ = l_Lean_Compiler_Bytecode_Instruction_sset8(v_target_boxed_248_, v_source_boxed_249_);
v_r_251_ = lean_box_uint32(v_res_250_);
return v_r_251_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sset16(uint32_t v_target_252_, uint32_t v_source_253_){
_start:
{
uint32_t v___x_254_; uint32_t v___x_255_; uint32_t v___x_256_; uint32_t v___x_257_; uint32_t v___x_258_; 
v___x_254_ = 1073741824;
v___x_255_ = 8;
v___x_256_ = lean_uint32_shift_left(v_target_252_, v___x_255_);
v___x_257_ = lean_uint32_lor(v___x_254_, v___x_256_);
v___x_258_ = lean_uint32_lor(v___x_257_, v_source_253_);
return v___x_258_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sset16_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_252_ = stack[0].m_num;
uint32_t v_source_253_ = stack[1].m_num;
uint32_t v_res_259_;
v_res_259_ = l_Lean_Compiler_Bytecode_Instruction_sset16(v_target_252_, v_source_253_);
stack->m_num = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset16___boxed(lean_object* v_target_260_, lean_object* v_source_261_){
_start:
{
uint32_t v_target_boxed_262_; uint32_t v_source_boxed_263_; uint32_t v_res_264_; lean_object* v_r_265_; 
v_target_boxed_262_ = lean_unbox_uint32(v_target_260_);
lean_dec(v_target_260_);
v_source_boxed_263_ = lean_unbox_uint32(v_source_261_);
lean_dec(v_source_261_);
v_res_264_ = l_Lean_Compiler_Bytecode_Instruction_sset16(v_target_boxed_262_, v_source_boxed_263_);
v_r_265_ = lean_box_uint32(v_res_264_);
return v_r_265_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sset32(uint32_t v_target_266_, uint32_t v_source_267_){
_start:
{
uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint32_t v___x_271_; uint32_t v___x_272_; 
v___x_268_ = 1140850688;
v___x_269_ = 8;
v___x_270_ = lean_uint32_shift_left(v_target_266_, v___x_269_);
v___x_271_ = lean_uint32_lor(v___x_268_, v___x_270_);
v___x_272_ = lean_uint32_lor(v___x_271_, v_source_267_);
return v___x_272_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sset32_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_266_ = stack[0].m_num;
uint32_t v_source_267_ = stack[1].m_num;
uint32_t v_res_273_;
v_res_273_ = l_Lean_Compiler_Bytecode_Instruction_sset32(v_target_266_, v_source_267_);
stack->m_num = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset32___boxed(lean_object* v_target_274_, lean_object* v_source_275_){
_start:
{
uint32_t v_target_boxed_276_; uint32_t v_source_boxed_277_; uint32_t v_res_278_; lean_object* v_r_279_; 
v_target_boxed_276_ = lean_unbox_uint32(v_target_274_);
lean_dec(v_target_274_);
v_source_boxed_277_ = lean_unbox_uint32(v_source_275_);
lean_dec(v_source_275_);
v_res_278_ = l_Lean_Compiler_Bytecode_Instruction_sset32(v_target_boxed_276_, v_source_boxed_277_);
v_r_279_ = lean_box_uint32(v_res_278_);
return v_r_279_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_sset64(uint32_t v_target_280_, uint32_t v_source_281_){
_start:
{
uint32_t v___x_282_; uint32_t v___x_283_; uint32_t v___x_284_; uint32_t v___x_285_; uint32_t v___x_286_; 
v___x_282_ = 1207959552;
v___x_283_ = 8;
v___x_284_ = lean_uint32_shift_left(v_target_280_, v___x_283_);
v___x_285_ = lean_uint32_lor(v___x_282_, v___x_284_);
v___x_286_ = lean_uint32_lor(v___x_285_, v_source_281_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_sset64_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_280_ = stack[0].m_num;
uint32_t v_source_281_ = stack[1].m_num;
uint32_t v_res_287_;
v_res_287_ = l_Lean_Compiler_Bytecode_Instruction_sset64(v_target_280_, v_source_281_);
stack->m_num = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset64___boxed(lean_object* v_target_288_, lean_object* v_source_289_){
_start:
{
uint32_t v_target_boxed_290_; uint32_t v_source_boxed_291_; uint32_t v_res_292_; lean_object* v_r_293_; 
v_target_boxed_290_ = lean_unbox_uint32(v_target_288_);
lean_dec(v_target_288_);
v_source_boxed_291_ = lean_unbox_uint32(v_source_289_);
lean_dec(v_source_289_);
v_res_292_ = l_Lean_Compiler_Bytecode_Instruction_sset64(v_target_boxed_290_, v_source_boxed_291_);
v_r_293_ = lean_box_uint32(v_res_292_);
return v_r_293_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxSmall(uint32_t v_target_294_, uint32_t v_source_295_){
_start:
{
uint32_t v___x_296_; uint32_t v___x_297_; uint32_t v___x_298_; uint32_t v___x_299_; uint32_t v___x_300_; 
v___x_296_ = 1275068416;
v___x_297_ = 8;
v___x_298_ = lean_uint32_shift_left(v_target_294_, v___x_297_);
v___x_299_ = lean_uint32_lor(v___x_296_, v___x_298_);
v___x_300_ = lean_uint32_lor(v___x_299_, v_source_295_);
return v___x_300_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_boxSmall_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_294_ = stack[0].m_num;
uint32_t v_source_295_ = stack[1].m_num;
uint32_t v_res_301_;
v_res_301_ = l_Lean_Compiler_Bytecode_Instruction_boxSmall(v_target_294_, v_source_295_);
stack->m_num = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxSmall___boxed(lean_object* v_target_302_, lean_object* v_source_303_){
_start:
{
uint32_t v_target_boxed_304_; uint32_t v_source_boxed_305_; uint32_t v_res_306_; lean_object* v_r_307_; 
v_target_boxed_304_ = lean_unbox_uint32(v_target_302_);
lean_dec(v_target_302_);
v_source_boxed_305_ = lean_unbox_uint32(v_source_303_);
lean_dec(v_source_303_);
v_res_306_ = l_Lean_Compiler_Bytecode_Instruction_boxSmall(v_target_boxed_304_, v_source_boxed_305_);
v_r_307_ = lean_box_uint32(v_res_306_);
return v_r_307_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt32(uint32_t v_target_308_, uint32_t v_source_309_){
_start:
{
uint32_t v___x_310_; uint32_t v___x_311_; uint32_t v___x_312_; uint32_t v___x_313_; uint32_t v___x_314_; 
v___x_310_ = 1342177280;
v___x_311_ = 8;
v___x_312_ = lean_uint32_shift_left(v_target_308_, v___x_311_);
v___x_313_ = lean_uint32_lor(v___x_310_, v___x_312_);
v___x_314_ = lean_uint32_lor(v___x_313_, v_source_309_);
return v___x_314_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_boxUInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_308_ = stack[0].m_num;
uint32_t v_source_309_ = stack[1].m_num;
uint32_t v_res_315_;
v_res_315_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt32(v_target_308_, v_source_309_);
stack->m_num = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt32___boxed(lean_object* v_target_316_, lean_object* v_source_317_){
_start:
{
uint32_t v_target_boxed_318_; uint32_t v_source_boxed_319_; uint32_t v_res_320_; lean_object* v_r_321_; 
v_target_boxed_318_ = lean_unbox_uint32(v_target_316_);
lean_dec(v_target_316_);
v_source_boxed_319_ = lean_unbox_uint32(v_source_317_);
lean_dec(v_source_317_);
v_res_320_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt32(v_target_boxed_318_, v_source_boxed_319_);
v_r_321_ = lean_box_uint32(v_res_320_);
return v_r_321_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt64(uint32_t v_target_322_, uint32_t v_source_323_){
_start:
{
uint32_t v___x_324_; uint32_t v___x_325_; uint32_t v___x_326_; uint32_t v___x_327_; uint32_t v___x_328_; 
v___x_324_ = 1409286144;
v___x_325_ = 8;
v___x_326_ = lean_uint32_shift_left(v_target_322_, v___x_325_);
v___x_327_ = lean_uint32_lor(v___x_324_, v___x_326_);
v___x_328_ = lean_uint32_lor(v___x_327_, v_source_323_);
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_boxUInt64_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_322_ = stack[0].m_num;
uint32_t v_source_323_ = stack[1].m_num;
uint32_t v_res_329_;
v_res_329_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt64(v_target_322_, v_source_323_);
stack->m_num = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt64___boxed(lean_object* v_target_330_, lean_object* v_source_331_){
_start:
{
uint32_t v_target_boxed_332_; uint32_t v_source_boxed_333_; uint32_t v_res_334_; lean_object* v_r_335_; 
v_target_boxed_332_ = lean_unbox_uint32(v_target_330_);
lean_dec(v_target_330_);
v_source_boxed_333_ = lean_unbox_uint32(v_source_331_);
lean_dec(v_source_331_);
v_res_334_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt64(v_target_boxed_332_, v_source_boxed_333_);
v_r_335_ = lean_box_uint32(v_res_334_);
return v_r_335_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUSize(uint32_t v_target_336_, uint32_t v_source_337_){
_start:
{
uint32_t v___x_338_; uint32_t v___x_339_; uint32_t v___x_340_; uint32_t v___x_341_; uint32_t v___x_342_; 
v___x_338_ = 1476395008;
v___x_339_ = 8;
v___x_340_ = lean_uint32_shift_left(v_target_336_, v___x_339_);
v___x_341_ = lean_uint32_lor(v___x_338_, v___x_340_);
v___x_342_ = lean_uint32_lor(v___x_341_, v_source_337_);
return v___x_342_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_boxUSize_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_336_ = stack[0].m_num;
uint32_t v_source_337_ = stack[1].m_num;
uint32_t v_res_343_;
v_res_343_ = l_Lean_Compiler_Bytecode_Instruction_boxUSize(v_target_336_, v_source_337_);
stack->m_num = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUSize___boxed(lean_object* v_target_344_, lean_object* v_source_345_){
_start:
{
uint32_t v_target_boxed_346_; uint32_t v_source_boxed_347_; uint32_t v_res_348_; lean_object* v_r_349_; 
v_target_boxed_346_ = lean_unbox_uint32(v_target_344_);
lean_dec(v_target_344_);
v_source_boxed_347_ = lean_unbox_uint32(v_source_345_);
lean_dec(v_source_345_);
v_res_348_ = l_Lean_Compiler_Bytecode_Instruction_boxUSize(v_target_boxed_346_, v_source_boxed_347_);
v_r_349_ = lean_box_uint32(v_res_348_);
return v_r_349_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat(uint32_t v_target_350_, uint32_t v_source_351_){
_start:
{
uint32_t v___x_352_; uint32_t v___x_353_; uint32_t v___x_354_; uint32_t v___x_355_; uint32_t v___x_356_; 
v___x_352_ = 1543503872;
v___x_353_ = 8;
v___x_354_ = lean_uint32_shift_left(v_target_350_, v___x_353_);
v___x_355_ = lean_uint32_lor(v___x_352_, v___x_354_);
v___x_356_ = lean_uint32_lor(v___x_355_, v_source_351_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_boxFloat_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_350_ = stack[0].m_num;
uint32_t v_source_351_ = stack[1].m_num;
uint32_t v_res_357_;
v_res_357_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat(v_target_350_, v_source_351_);
stack->m_num = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat___boxed(lean_object* v_target_358_, lean_object* v_source_359_){
_start:
{
uint32_t v_target_boxed_360_; uint32_t v_source_boxed_361_; uint32_t v_res_362_; lean_object* v_r_363_; 
v_target_boxed_360_ = lean_unbox_uint32(v_target_358_);
lean_dec(v_target_358_);
v_source_boxed_361_ = lean_unbox_uint32(v_source_359_);
lean_dec(v_source_359_);
v_res_362_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat(v_target_boxed_360_, v_source_boxed_361_);
v_r_363_ = lean_box_uint32(v_res_362_);
return v_r_363_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat32(uint32_t v_target_364_, uint32_t v_source_365_){
_start:
{
uint32_t v___x_366_; uint32_t v___x_367_; uint32_t v___x_368_; uint32_t v___x_369_; uint32_t v___x_370_; 
v___x_366_ = 1610612736;
v___x_367_ = 8;
v___x_368_ = lean_uint32_shift_left(v_target_364_, v___x_367_);
v___x_369_ = lean_uint32_lor(v___x_366_, v___x_368_);
v___x_370_ = lean_uint32_lor(v___x_369_, v_source_365_);
return v___x_370_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_boxFloat32_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_364_ = stack[0].m_num;
uint32_t v_source_365_ = stack[1].m_num;
uint32_t v_res_371_;
v_res_371_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat32(v_target_364_, v_source_365_);
stack->m_num = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat32___boxed(lean_object* v_target_372_, lean_object* v_source_373_){
_start:
{
uint32_t v_target_boxed_374_; uint32_t v_source_boxed_375_; uint32_t v_res_376_; lean_object* v_r_377_; 
v_target_boxed_374_ = lean_unbox_uint32(v_target_372_);
lean_dec(v_target_372_);
v_source_boxed_375_ = lean_unbox_uint32(v_source_373_);
lean_dec(v_source_373_);
v_res_376_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat32(v_target_boxed_374_, v_source_boxed_375_);
v_r_377_ = lean_box_uint32(v_res_376_);
return v_r_377_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxSmall(uint32_t v_target_378_, uint32_t v_source_379_){
_start:
{
uint32_t v___x_380_; uint32_t v___x_381_; uint32_t v___x_382_; uint32_t v___x_383_; uint32_t v___x_384_; 
v___x_380_ = 1677721600;
v___x_381_ = 8;
v___x_382_ = lean_uint32_shift_left(v_target_378_, v___x_381_);
v___x_383_ = lean_uint32_lor(v___x_380_, v___x_382_);
v___x_384_ = lean_uint32_lor(v___x_383_, v_source_379_);
return v___x_384_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_unboxSmall_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_378_ = stack[0].m_num;
uint32_t v_source_379_ = stack[1].m_num;
uint32_t v_res_385_;
v_res_385_ = l_Lean_Compiler_Bytecode_Instruction_unboxSmall(v_target_378_, v_source_379_);
stack->m_num = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxSmall___boxed(lean_object* v_target_386_, lean_object* v_source_387_){
_start:
{
uint32_t v_target_boxed_388_; uint32_t v_source_boxed_389_; uint32_t v_res_390_; lean_object* v_r_391_; 
v_target_boxed_388_ = lean_unbox_uint32(v_target_386_);
lean_dec(v_target_386_);
v_source_boxed_389_ = lean_unbox_uint32(v_source_387_);
lean_dec(v_source_387_);
v_res_390_ = l_Lean_Compiler_Bytecode_Instruction_unboxSmall(v_target_boxed_388_, v_source_boxed_389_);
v_r_391_ = lean_box_uint32(v_res_390_);
return v_r_391_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(uint32_t v_target_392_, uint32_t v_source_393_){
_start:
{
uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint32_t v___x_398_; 
v___x_394_ = 1744830464;
v___x_395_ = 8;
v___x_396_ = lean_uint32_shift_left(v_target_392_, v___x_395_);
v___x_397_ = lean_uint32_lor(v___x_394_, v___x_396_);
v___x_398_ = lean_uint32_lor(v___x_397_, v_source_393_);
return v___x_398_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_unboxUInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_392_ = stack[0].m_num;
uint32_t v_source_393_ = stack[1].m_num;
uint32_t v_res_399_;
v_res_399_ = l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(v_target_392_, v_source_393_);
stack->m_num = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt32___boxed(lean_object* v_target_400_, lean_object* v_source_401_){
_start:
{
uint32_t v_target_boxed_402_; uint32_t v_source_boxed_403_; uint32_t v_res_404_; lean_object* v_r_405_; 
v_target_boxed_402_ = lean_unbox_uint32(v_target_400_);
lean_dec(v_target_400_);
v_source_boxed_403_ = lean_unbox_uint32(v_source_401_);
lean_dec(v_source_401_);
v_res_404_ = l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(v_target_boxed_402_, v_source_boxed_403_);
v_r_405_ = lean_box_uint32(v_res_404_);
return v_r_405_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(uint32_t v_target_406_, uint32_t v_source_407_){
_start:
{
uint32_t v___x_408_; uint32_t v___x_409_; uint32_t v___x_410_; uint32_t v___x_411_; uint32_t v___x_412_; 
v___x_408_ = 1811939328;
v___x_409_ = 8;
v___x_410_ = lean_uint32_shift_left(v_target_406_, v___x_409_);
v___x_411_ = lean_uint32_lor(v___x_408_, v___x_410_);
v___x_412_ = lean_uint32_lor(v___x_411_, v_source_407_);
return v___x_412_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_unboxUInt64_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_406_ = stack[0].m_num;
uint32_t v_source_407_ = stack[1].m_num;
uint32_t v_res_413_;
v_res_413_ = l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(v_target_406_, v_source_407_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt64___boxed(lean_object* v_target_414_, lean_object* v_source_415_){
_start:
{
uint32_t v_target_boxed_416_; uint32_t v_source_boxed_417_; uint32_t v_res_418_; lean_object* v_r_419_; 
v_target_boxed_416_ = lean_unbox_uint32(v_target_414_);
lean_dec(v_target_414_);
v_source_boxed_417_ = lean_unbox_uint32(v_source_415_);
lean_dec(v_source_415_);
v_res_418_ = l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(v_target_boxed_416_, v_source_boxed_417_);
v_r_419_ = lean_box_uint32(v_res_418_);
return v_r_419_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUSize(uint32_t v_target_420_, uint32_t v_source_421_){
_start:
{
uint32_t v___x_422_; uint32_t v___x_423_; uint32_t v___x_424_; uint32_t v___x_425_; uint32_t v___x_426_; 
v___x_422_ = 1879048192;
v___x_423_ = 8;
v___x_424_ = lean_uint32_shift_left(v_target_420_, v___x_423_);
v___x_425_ = lean_uint32_lor(v___x_422_, v___x_424_);
v___x_426_ = lean_uint32_lor(v___x_425_, v_source_421_);
return v___x_426_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_unboxUSize_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_420_ = stack[0].m_num;
uint32_t v_source_421_ = stack[1].m_num;
uint32_t v_res_427_;
v_res_427_ = l_Lean_Compiler_Bytecode_Instruction_unboxUSize(v_target_420_, v_source_421_);
stack->m_num = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUSize___boxed(lean_object* v_target_428_, lean_object* v_source_429_){
_start:
{
uint32_t v_target_boxed_430_; uint32_t v_source_boxed_431_; uint32_t v_res_432_; lean_object* v_r_433_; 
v_target_boxed_430_ = lean_unbox_uint32(v_target_428_);
lean_dec(v_target_428_);
v_source_boxed_431_ = lean_unbox_uint32(v_source_429_);
lean_dec(v_source_429_);
v_res_432_ = l_Lean_Compiler_Bytecode_Instruction_unboxUSize(v_target_boxed_430_, v_source_boxed_431_);
v_r_433_ = lean_box_uint32(v_res_432_);
return v_r_433_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat(uint32_t v_target_434_, uint32_t v_source_435_){
_start:
{
uint32_t v___x_436_; uint32_t v___x_437_; uint32_t v___x_438_; uint32_t v___x_439_; uint32_t v___x_440_; 
v___x_436_ = 1946157056;
v___x_437_ = 8;
v___x_438_ = lean_uint32_shift_left(v_target_434_, v___x_437_);
v___x_439_ = lean_uint32_lor(v___x_436_, v___x_438_);
v___x_440_ = lean_uint32_lor(v___x_439_, v_source_435_);
return v___x_440_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_unboxFloat_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_434_ = stack[0].m_num;
uint32_t v_source_435_ = stack[1].m_num;
uint32_t v_res_441_;
v_res_441_ = l_Lean_Compiler_Bytecode_Instruction_unboxFloat(v_target_434_, v_source_435_);
stack->m_num = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat___boxed(lean_object* v_target_442_, lean_object* v_source_443_){
_start:
{
uint32_t v_target_boxed_444_; uint32_t v_source_boxed_445_; uint32_t v_res_446_; lean_object* v_r_447_; 
v_target_boxed_444_ = lean_unbox_uint32(v_target_442_);
lean_dec(v_target_442_);
v_source_boxed_445_ = lean_unbox_uint32(v_source_443_);
lean_dec(v_source_443_);
v_res_446_ = l_Lean_Compiler_Bytecode_Instruction_unboxFloat(v_target_boxed_444_, v_source_boxed_445_);
v_r_447_ = lean_box_uint32(v_res_446_);
return v_r_447_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(uint32_t v_target_448_, uint32_t v_source_449_){
_start:
{
uint32_t v___x_450_; uint32_t v___x_451_; uint32_t v___x_452_; uint32_t v___x_453_; uint32_t v___x_454_; 
v___x_450_ = 2013265920;
v___x_451_ = 8;
v___x_452_ = lean_uint32_shift_left(v_target_448_, v___x_451_);
v___x_453_ = lean_uint32_lor(v___x_450_, v___x_452_);
v___x_454_ = lean_uint32_lor(v___x_453_, v_source_449_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_unboxFloat32_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_448_ = stack[0].m_num;
uint32_t v_source_449_ = stack[1].m_num;
uint32_t v_res_455_;
v_res_455_ = l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(v_target_448_, v_source_449_);
stack->m_num = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat32___boxed(lean_object* v_target_456_, lean_object* v_source_457_){
_start:
{
uint32_t v_target_boxed_458_; uint32_t v_source_boxed_459_; uint32_t v_res_460_; lean_object* v_r_461_; 
v_target_boxed_458_ = lean_unbox_uint32(v_target_456_);
lean_dec(v_target_456_);
v_source_boxed_459_ = lean_unbox_uint32(v_source_457_);
lean_dec(v_source_457_);
v_res_460_ = l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(v_target_boxed_458_, v_source_boxed_459_);
v_r_461_ = lean_box_uint32(v_res_460_);
return v_r_461_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_inc(uint32_t v_target_462_, uint32_t v_count_463_){
_start:
{
uint32_t v___x_464_; uint32_t v___x_465_; uint32_t v___x_466_; uint32_t v___x_467_; uint32_t v___x_468_; 
v___x_464_ = 2080374784;
v___x_465_ = 8;
v___x_466_ = lean_uint32_shift_left(v_target_462_, v___x_465_);
v___x_467_ = lean_uint32_lor(v___x_464_, v___x_466_);
v___x_468_ = lean_uint32_lor(v___x_467_, v_count_463_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_inc_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_462_ = stack[0].m_num;
uint32_t v_count_463_ = stack[1].m_num;
uint32_t v_res_469_;
v_res_469_ = l_Lean_Compiler_Bytecode_Instruction_inc(v_target_462_, v_count_463_);
stack->m_num = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_inc___boxed(lean_object* v_target_470_, lean_object* v_count_471_){
_start:
{
uint32_t v_target_boxed_472_; uint32_t v_count_boxed_473_; uint32_t v_res_474_; lean_object* v_r_475_; 
v_target_boxed_472_ = lean_unbox_uint32(v_target_470_);
lean_dec(v_target_470_);
v_count_boxed_473_ = lean_unbox_uint32(v_count_471_);
lean_dec(v_count_471_);
v_res_474_ = l_Lean_Compiler_Bytecode_Instruction_inc(v_target_boxed_472_, v_count_boxed_473_);
v_r_475_ = lean_box_uint32(v_res_474_);
return v_r_475_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_dec(uint32_t v_target_476_, uint32_t v_count_477_){
_start:
{
uint32_t v___x_478_; uint32_t v___x_479_; uint32_t v___x_480_; uint32_t v___x_481_; uint32_t v___x_482_; 
v___x_478_ = 2147483648;
v___x_479_ = 8;
v___x_480_ = lean_uint32_shift_left(v_target_476_, v___x_479_);
v___x_481_ = lean_uint32_lor(v___x_478_, v___x_480_);
v___x_482_ = lean_uint32_lor(v___x_481_, v_count_477_);
return v___x_482_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_dec_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_476_ = stack[0].m_num;
uint32_t v_count_477_ = stack[1].m_num;
uint32_t v_res_483_;
v_res_483_ = l_Lean_Compiler_Bytecode_Instruction_dec(v_target_476_, v_count_477_);
stack->m_num = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_dec___boxed(lean_object* v_target_484_, lean_object* v_count_485_){
_start:
{
uint32_t v_target_boxed_486_; uint32_t v_count_boxed_487_; uint32_t v_res_488_; lean_object* v_r_489_; 
v_target_boxed_486_ = lean_unbox_uint32(v_target_484_);
lean_dec(v_target_484_);
v_count_boxed_487_ = lean_unbox_uint32(v_count_485_);
lean_dec(v_count_485_);
v_res_488_ = l_Lean_Compiler_Bytecode_Instruction_dec(v_target_boxed_486_, v_count_boxed_487_);
v_r_489_ = lean_box_uint32(v_res_488_);
return v_r_489_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_isShared(uint32_t v_target_490_, uint32_t v_source_491_){
_start:
{
uint32_t v___x_492_; uint32_t v___x_493_; uint32_t v___x_494_; uint32_t v___x_495_; uint32_t v___x_496_; 
v___x_492_ = 2214592512;
v___x_493_ = 8;
v___x_494_ = lean_uint32_shift_left(v_target_490_, v___x_493_);
v___x_495_ = lean_uint32_lor(v___x_492_, v___x_494_);
v___x_496_ = lean_uint32_lor(v___x_495_, v_source_491_);
return v___x_496_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_isShared_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_490_ = stack[0].m_num;
uint32_t v_source_491_ = stack[1].m_num;
uint32_t v_res_497_;
v_res_497_ = l_Lean_Compiler_Bytecode_Instruction_isShared(v_target_490_, v_source_491_);
stack->m_num = v_res_497_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_isShared___boxed(lean_object* v_target_498_, lean_object* v_source_499_){
_start:
{
uint32_t v_target_boxed_500_; uint32_t v_source_boxed_501_; uint32_t v_res_502_; lean_object* v_r_503_; 
v_target_boxed_500_ = lean_unbox_uint32(v_target_498_);
lean_dec(v_target_498_);
v_source_boxed_501_ = lean_unbox_uint32(v_source_499_);
lean_dec(v_source_499_);
v_res_502_ = l_Lean_Compiler_Bytecode_Instruction_isShared(v_target_boxed_500_, v_source_boxed_501_);
v_r_503_ = lean_box_uint32(v_res_502_);
return v_r_503_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_loadTag(uint32_t v_target_504_, uint32_t v_source_505_){
_start:
{
uint32_t v___x_506_; uint32_t v___x_507_; uint32_t v___x_508_; uint32_t v___x_509_; uint32_t v___x_510_; 
v___x_506_ = 2281701376;
v___x_507_ = 8;
v___x_508_ = lean_uint32_shift_left(v_target_504_, v___x_507_);
v___x_509_ = lean_uint32_lor(v___x_506_, v___x_508_);
v___x_510_ = lean_uint32_lor(v___x_509_, v_source_505_);
return v___x_510_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_loadTag_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_504_ = stack[0].m_num;
uint32_t v_source_505_ = stack[1].m_num;
uint32_t v_res_511_;
v_res_511_ = l_Lean_Compiler_Bytecode_Instruction_loadTag(v_target_504_, v_source_505_);
stack->m_num = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadTag___boxed(lean_object* v_target_512_, lean_object* v_source_513_){
_start:
{
uint32_t v_target_boxed_514_; uint32_t v_source_boxed_515_; uint32_t v_res_516_; lean_object* v_r_517_; 
v_target_boxed_514_ = lean_unbox_uint32(v_target_512_);
lean_dec(v_target_512_);
v_source_boxed_515_ = lean_unbox_uint32(v_source_513_);
lean_dec(v_source_513_);
v_res_516_ = l_Lean_Compiler_Bytecode_Instruction_loadTag(v_target_boxed_514_, v_source_boxed_515_);
v_r_517_ = lean_box_uint32(v_res_516_);
return v_r_517_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_jumpTable(uint32_t v_source_518_, uint32_t v_limit_519_){
_start:
{
uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; 
v___x_520_ = 2348810240;
v___x_521_ = 10;
v___x_522_ = lean_uint32_shift_left(v_source_518_, v___x_521_);
v___x_523_ = lean_uint32_lor(v___x_520_, v___x_522_);
v___x_524_ = lean_uint32_lor(v___x_523_, v_limit_519_);
return v___x_524_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_jumpTable_0interp(lean_interpreter_value* stack)
{
uint32_t v_source_518_ = stack[0].m_num;
uint32_t v_limit_519_ = stack[1].m_num;
uint32_t v_res_525_;
v_res_525_ = l_Lean_Compiler_Bytecode_Instruction_jumpTable(v_source_518_, v_limit_519_);
stack->m_num = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jumpTable___boxed(lean_object* v_source_526_, lean_object* v_limit_527_){
_start:
{
uint32_t v_source_boxed_528_; uint32_t v_limit_boxed_529_; uint32_t v_res_530_; lean_object* v_r_531_; 
v_source_boxed_528_ = lean_unbox_uint32(v_source_526_);
lean_dec(v_source_526_);
v_limit_boxed_529_ = lean_unbox_uint32(v_limit_527_);
lean_dec(v_limit_527_);
v_res_530_ = l_Lean_Compiler_Bytecode_Instruction_jumpTable(v_source_boxed_528_, v_limit_boxed_529_);
v_r_531_ = lean_box_uint32(v_res_530_);
return v_r_531_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_setTag(uint32_t v_target_532_, uint32_t v_tag_533_){
_start:
{
uint32_t v___x_534_; uint32_t v___x_535_; uint32_t v___x_536_; uint32_t v___x_537_; uint32_t v___x_538_; 
v___x_534_ = 2415919104;
v___x_535_ = 10;
v___x_536_ = lean_uint32_shift_left(v_target_532_, v___x_535_);
v___x_537_ = lean_uint32_lor(v___x_534_, v___x_536_);
v___x_538_ = lean_uint32_lor(v___x_537_, v_tag_533_);
return v___x_538_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_setTag_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_532_ = stack[0].m_num;
uint32_t v_tag_533_ = stack[1].m_num;
uint32_t v_res_539_;
v_res_539_ = l_Lean_Compiler_Bytecode_Instruction_setTag(v_target_532_, v_tag_533_);
stack->m_num = v_res_539_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_setTag___boxed(lean_object* v_target_540_, lean_object* v_tag_541_){
_start:
{
uint32_t v_target_boxed_542_; uint32_t v_tag_boxed_543_; uint32_t v_res_544_; lean_object* v_r_545_; 
v_target_boxed_542_ = lean_unbox_uint32(v_target_540_);
lean_dec(v_target_540_);
v_tag_boxed_543_ = lean_unbox_uint32(v_tag_541_);
lean_dec(v_tag_541_);
v_res_544_ = l_Lean_Compiler_Bytecode_Instruction_setTag(v_target_boxed_542_, v_tag_boxed_543_);
v_r_545_ = lean_box_uint32(v_res_544_);
return v_r_545_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_loadConst(uint32_t v_fn_546_){
_start:
{
uint32_t v___x_547_; uint32_t v___x_548_; 
v___x_547_ = 2483027968;
v___x_548_ = lean_uint32_lor(v___x_547_, v_fn_546_);
return v___x_548_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_loadConst_0interp(lean_interpreter_value* stack)
{
uint32_t v_fn_546_ = stack[0].m_num;
uint32_t v_res_549_;
v_res_549_ = l_Lean_Compiler_Bytecode_Instruction_loadConst(v_fn_546_);
stack->m_num = v_res_549_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadConst___boxed(lean_object* v_fn_550_){
_start:
{
uint32_t v_fn_boxed_551_; uint32_t v_res_552_; lean_object* v_r_553_; 
v_fn_boxed_551_ = lean_unbox_uint32(v_fn_550_);
lean_dec(v_fn_550_);
v_res_552_ = l_Lean_Compiler_Bytecode_Instruction_loadConst(v_fn_boxed_551_);
v_r_553_ = lean_box_uint32(v_res_552_);
return v_r_553_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0(void){
_start:
{
lean_object* v___x_554_; uint32_t v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(128u);
v___x_555_ = lean_int32_of_nat(v___x_554_);
return v___x_555_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_ifTag(uint32_t v_target_556_, uint32_t v_tag_557_, uint32_t v_offset_558_){
_start:
{
uint32_t v___x_559_; uint32_t v___x_560_; uint32_t v___x_561_; uint32_t v___x_562_; uint32_t v___x_563_; uint32_t v___x_564_; uint32_t v___x_565_; uint32_t v___x_566_; uint32_t v___x_567_; uint32_t v___x_568_; 
v___x_559_ = 2550136832;
v___x_560_ = 18;
v___x_561_ = lean_uint32_shift_left(v_target_556_, v___x_560_);
v___x_562_ = lean_uint32_lor(v___x_559_, v___x_561_);
v___x_563_ = 8;
v___x_564_ = lean_uint32_shift_left(v_tag_557_, v___x_563_);
v___x_565_ = lean_uint32_lor(v___x_562_, v___x_564_);
v___x_566_ = lean_uint32_once(&l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0, &l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0_once, _init_l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0);
v___x_567_ = lean_int32_add(v_offset_558_, v___x_566_);
v___x_568_ = lean_uint32_lor(v___x_565_, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_ifTag_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_556_ = stack[0].m_num;
uint32_t v_tag_557_ = stack[1].m_num;
uint32_t v_offset_558_ = stack[2].m_num;
uint32_t v_res_569_;
v_res_569_ = l_Lean_Compiler_Bytecode_Instruction_ifTag(v_target_556_, v_tag_557_, v_offset_558_);
stack->m_num = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ifTag___boxed(lean_object* v_target_570_, lean_object* v_tag_571_, lean_object* v_offset_572_){
_start:
{
uint32_t v_target_boxed_573_; uint32_t v_tag_boxed_574_; uint32_t v_offset_boxed_575_; uint32_t v_res_576_; lean_object* v_r_577_; 
v_target_boxed_573_ = lean_unbox_uint32(v_target_570_);
lean_dec(v_target_570_);
v_tag_boxed_574_ = lean_unbox_uint32(v_tag_571_);
lean_dec(v_tag_571_);
v_offset_boxed_575_ = lean_unbox_uint32(v_offset_572_);
lean_dec(v_offset_572_);
v_res_576_ = l_Lean_Compiler_Bytecode_Instruction_ifTag(v_target_boxed_573_, v_tag_boxed_574_, v_offset_boxed_575_);
v_r_577_ = lean_box_uint32(v_res_576_);
return v_r_577_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_Instruction_jump___closed__0(void){
_start:
{
lean_object* v___x_578_; uint32_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(33554432u);
v___x_579_ = lean_int32_of_nat(v___x_578_);
return v___x_579_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_jump(uint32_t v_offset_580_){
_start:
{
uint32_t v___x_581_; uint32_t v___x_582_; uint32_t v___x_583_; uint32_t v___x_584_; 
v___x_581_ = 2617245696;
v___x_582_ = lean_uint32_once(&l_Lean_Compiler_Bytecode_Instruction_jump___closed__0, &l_Lean_Compiler_Bytecode_Instruction_jump___closed__0_once, _init_l_Lean_Compiler_Bytecode_Instruction_jump___closed__0);
v___x_583_ = lean_int32_add(v_offset_580_, v___x_582_);
v___x_584_ = lean_uint32_lor(v___x_581_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_jump_0interp(lean_interpreter_value* stack)
{
uint32_t v_offset_580_ = stack[0].m_num;
uint32_t v_res_585_;
v_res_585_ = l_Lean_Compiler_Bytecode_Instruction_jump(v_offset_580_);
stack->m_num = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jump___boxed(lean_object* v_offset_586_){
_start:
{
uint32_t v_offset_boxed_587_; uint32_t v_res_588_; lean_object* v_r_589_; 
v_offset_boxed_587_ = lean_unbox_uint32(v_offset_586_);
lean_dec(v_offset_586_);
v_res_588_ = l_Lean_Compiler_Bytecode_Instruction_jump(v_offset_boxed_587_);
v_r_589_ = lean_box_uint32(v_res_588_);
return v_r_589_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_Instruction_nojump(void){
_start:
{
uint32_t v___x_590_; 
v___x_590_ = 2617245696;
return v___x_590_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_app(uint32_t v_fn_591_, uint32_t v_n_592_){
_start:
{
uint32_t v___x_593_; uint32_t v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint32_t v___x_597_; 
v___x_593_ = 2684354560;
v___x_594_ = 16;
v___x_595_ = lean_uint32_shift_left(v_n_592_, v___x_594_);
v___x_596_ = lean_uint32_lor(v___x_593_, v___x_595_);
v___x_597_ = lean_uint32_lor(v___x_596_, v_fn_591_);
return v___x_597_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_app_0interp(lean_interpreter_value* stack)
{
uint32_t v_fn_591_ = stack[0].m_num;
uint32_t v_n_592_ = stack[1].m_num;
uint32_t v_res_598_;
v_res_598_ = l_Lean_Compiler_Bytecode_Instruction_app(v_fn_591_, v_n_592_);
stack->m_num = v_res_598_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_app___boxed(lean_object* v_fn_599_, lean_object* v_n_600_){
_start:
{
uint32_t v_fn_boxed_601_; uint32_t v_n_boxed_602_; uint32_t v_res_603_; lean_object* v_r_604_; 
v_fn_boxed_601_ = lean_unbox_uint32(v_fn_599_);
lean_dec(v_fn_599_);
v_n_boxed_602_ = lean_unbox_uint32(v_n_600_);
lean_dec(v_n_600_);
v_res_603_ = l_Lean_Compiler_Bytecode_Instruction_app(v_fn_boxed_601_, v_n_boxed_602_);
v_r_604_ = lean_box_uint32(v_res_603_);
return v_r_604_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_pap(uint32_t v_fn_605_, uint32_t v_n_606_){
_start:
{
uint32_t v___x_607_; uint32_t v___x_608_; uint32_t v___x_609_; uint32_t v___x_610_; uint32_t v___x_611_; 
v___x_607_ = 2751463424;
v___x_608_ = 16;
v___x_609_ = lean_uint32_shift_left(v_n_606_, v___x_608_);
v___x_610_ = lean_uint32_lor(v___x_607_, v___x_609_);
v___x_611_ = lean_uint32_lor(v___x_610_, v_fn_605_);
return v___x_611_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_pap_0interp(lean_interpreter_value* stack)
{
uint32_t v_fn_605_ = stack[0].m_num;
uint32_t v_n_606_ = stack[1].m_num;
uint32_t v_res_612_;
v_res_612_ = l_Lean_Compiler_Bytecode_Instruction_pap(v_fn_605_, v_n_606_);
stack->m_num = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_pap___boxed(lean_object* v_fn_613_, lean_object* v_n_614_){
_start:
{
uint32_t v_fn_boxed_615_; uint32_t v_n_boxed_616_; uint32_t v_res_617_; lean_object* v_r_618_; 
v_fn_boxed_615_ = lean_unbox_uint32(v_fn_613_);
lean_dec(v_fn_613_);
v_n_boxed_616_ = lean_unbox_uint32(v_n_614_);
lean_dec(v_n_614_);
v_res_617_ = l_Lean_Compiler_Bytecode_Instruction_pap(v_fn_boxed_615_, v_n_boxed_616_);
v_r_618_ = lean_box_uint32(v_res_617_);
return v_r_618_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_del(uint32_t v_target_619_){
_start:
{
uint32_t v___x_620_; uint32_t v___x_621_; 
v___x_620_ = 2818572288;
v___x_621_ = lean_uint32_lor(v___x_620_, v_target_619_);
return v___x_621_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_del_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_619_ = stack[0].m_num;
uint32_t v_res_622_;
v_res_622_ = l_Lean_Compiler_Bytecode_Instruction_del(v_target_619_);
stack->m_num = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_del___boxed(lean_object* v_target_623_){
_start:
{
uint32_t v_target_boxed_624_; uint32_t v_res_625_; lean_object* v_r_626_; 
v_target_boxed_624_ = lean_unbox_uint32(v_target_623_);
lean_dec(v_target_623_);
v_res_625_ = l_Lean_Compiler_Bytecode_Instruction_del(v_target_boxed_624_);
v_r_626_ = lean_box_uint32(v_res_625_);
return v_r_626_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_reset(uint32_t v_n_627_, uint32_t v_target_628_, uint32_t v_source_629_){
_start:
{
uint32_t v___x_630_; uint32_t v___x_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint32_t v___x_636_; uint32_t v___x_637_; 
v___x_630_ = 2885681152;
v___x_631_ = 16;
v___x_632_ = lean_uint32_shift_left(v_n_627_, v___x_631_);
v___x_633_ = lean_uint32_lor(v___x_630_, v___x_632_);
v___x_634_ = 8;
v___x_635_ = lean_uint32_shift_left(v_target_628_, v___x_634_);
v___x_636_ = lean_uint32_lor(v___x_633_, v___x_635_);
v___x_637_ = lean_uint32_lor(v___x_636_, v_source_629_);
return v___x_637_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_reset_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_627_ = stack[0].m_num;
uint32_t v_target_628_ = stack[1].m_num;
uint32_t v_source_629_ = stack[2].m_num;
uint32_t v_res_638_;
v_res_638_ = l_Lean_Compiler_Bytecode_Instruction_reset(v_n_627_, v_target_628_, v_source_629_);
stack->m_num = v_res_638_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reset___boxed(lean_object* v_n_639_, lean_object* v_target_640_, lean_object* v_source_641_){
_start:
{
uint32_t v_n_boxed_642_; uint32_t v_target_boxed_643_; uint32_t v_source_boxed_644_; uint32_t v_res_645_; lean_object* v_r_646_; 
v_n_boxed_642_ = lean_unbox_uint32(v_n_639_);
lean_dec(v_n_639_);
v_target_boxed_643_ = lean_unbox_uint32(v_target_640_);
lean_dec(v_target_640_);
v_source_boxed_644_ = lean_unbox_uint32(v_source_641_);
lean_dec(v_source_641_);
v_res_645_ = l_Lean_Compiler_Bytecode_Instruction_reset(v_n_boxed_642_, v_target_boxed_643_, v_source_boxed_644_);
v_r_646_ = lean_box_uint32(v_res_645_);
return v_r_646_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_reuse(uint32_t v_target_647_, uint32_t v_tag_648_, uint32_t v_numObjs_649_){
_start:
{
uint32_t v___x_650_; uint32_t v___x_651_; uint32_t v___x_652_; uint32_t v___x_653_; uint32_t v___x_654_; uint32_t v___x_655_; uint32_t v___x_656_; uint32_t v___x_657_; 
v___x_650_ = 2952790016;
v___x_651_ = 18;
v___x_652_ = lean_uint32_shift_left(v_target_647_, v___x_651_);
v___x_653_ = lean_uint32_lor(v___x_650_, v___x_652_);
v___x_654_ = 8;
v___x_655_ = lean_uint32_shift_left(v_tag_648_, v___x_654_);
v___x_656_ = lean_uint32_lor(v___x_653_, v___x_655_);
v___x_657_ = lean_uint32_lor(v___x_656_, v_numObjs_649_);
return v___x_657_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_reuse_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_647_ = stack[0].m_num;
uint32_t v_tag_648_ = stack[1].m_num;
uint32_t v_numObjs_649_ = stack[2].m_num;
uint32_t v_res_658_;
v_res_658_ = l_Lean_Compiler_Bytecode_Instruction_reuse(v_target_647_, v_tag_648_, v_numObjs_649_);
stack->m_num = v_res_658_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reuse___boxed(lean_object* v_target_659_, lean_object* v_tag_660_, lean_object* v_numObjs_661_){
_start:
{
uint32_t v_target_boxed_662_; uint32_t v_tag_boxed_663_; uint32_t v_numObjs_boxed_664_; uint32_t v_res_665_; lean_object* v_r_666_; 
v_target_boxed_662_ = lean_unbox_uint32(v_target_659_);
lean_dec(v_target_659_);
v_tag_boxed_663_ = lean_unbox_uint32(v_tag_660_);
lean_dec(v_tag_660_);
v_numObjs_boxed_664_ = lean_unbox_uint32(v_numObjs_661_);
lean_dec(v_numObjs_661_);
v_res_665_ = l_Lean_Compiler_Bytecode_Instruction_reuse(v_target_boxed_662_, v_tag_boxed_663_, v_numObjs_boxed_664_);
v_r_666_ = lean_box_uint32(v_res_665_);
return v_r_666_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_storeCache(uint32_t v_target_667_){
_start:
{
uint32_t v___x_668_; uint32_t v___x_669_; 
v___x_668_ = 3019898880;
v___x_669_ = lean_uint32_lor(v___x_668_, v_target_667_);
return v___x_669_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_storeCache_0interp(lean_interpreter_value* stack)
{
uint32_t v_target_667_ = stack[0].m_num;
uint32_t v_res_670_;
v_res_670_ = l_Lean_Compiler_Bytecode_Instruction_storeCache(v_target_667_);
stack->m_num = v_res_670_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_storeCache___boxed(lean_object* v_target_671_){
_start:
{
uint32_t v_target_boxed_672_; uint32_t v_res_673_; lean_object* v_r_674_; 
v_target_boxed_672_ = lean_unbox_uint32(v_target_671_);
lean_dec(v_target_671_);
v_res_673_ = l_Lean_Compiler_Bytecode_Instruction_storeCache(v_target_boxed_672_);
v_r_674_ = lean_box_uint32(v_res_673_);
return v_r_674_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_skipIfCached(uint32_t v_offset_675_){
_start:
{
uint32_t v___x_676_; uint32_t v___x_677_; 
v___x_676_ = 3087007744;
v___x_677_ = lean_uint32_lor(v___x_676_, v_offset_675_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_skipIfCached_0interp(lean_interpreter_value* stack)
{
uint32_t v_offset_675_ = stack[0].m_num;
uint32_t v_res_678_;
v_res_678_ = l_Lean_Compiler_Bytecode_Instruction_skipIfCached(v_offset_675_);
stack->m_num = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_skipIfCached___boxed(lean_object* v_offset_679_){
_start:
{
uint32_t v_offset_boxed_680_; uint32_t v_res_681_; lean_object* v_r_682_; 
v_offset_boxed_680_ = lean_unbox_uint32(v_offset_679_);
lean_dec(v_offset_679_);
v_res_681_ = l_Lean_Compiler_Bytecode_Instruction_skipIfCached(v_offset_boxed_680_);
v_r_682_ = lean_box_uint32(v_res_681_);
return v_r_682_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_declConst(uint32_t v_tgt_683_, uint32_t v_id_684_){
_start:
{
uint32_t v___x_685_; uint32_t v___x_686_; uint32_t v___x_687_; uint32_t v___x_688_; uint32_t v___x_689_; 
v___x_685_ = 3154116608;
v___x_686_ = 18;
v___x_687_ = lean_uint32_shift_left(v_tgt_683_, v___x_686_);
v___x_688_ = lean_uint32_lor(v___x_685_, v___x_687_);
v___x_689_ = lean_uint32_lor(v___x_688_, v_id_684_);
return v___x_689_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_declConst_0interp(lean_interpreter_value* stack)
{
uint32_t v_tgt_683_ = stack[0].m_num;
uint32_t v_id_684_ = stack[1].m_num;
uint32_t v_res_690_;
v_res_690_ = l_Lean_Compiler_Bytecode_Instruction_declConst(v_tgt_683_, v_id_684_);
stack->m_num = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_declConst___boxed(lean_object* v_tgt_691_, lean_object* v_id_692_){
_start:
{
uint32_t v_tgt_boxed_693_; uint32_t v_id_boxed_694_; uint32_t v_res_695_; lean_object* v_r_696_; 
v_tgt_boxed_693_ = lean_unbox_uint32(v_tgt_691_);
lean_dec(v_tgt_691_);
v_id_boxed_694_ = lean_unbox_uint32(v_id_692_);
lean_dec(v_id_692_);
v_res_695_ = l_Lean_Compiler_Bytecode_Instruction_declConst(v_tgt_boxed_693_, v_id_boxed_694_);
v_r_696_ = lean_box_uint32(v_res_695_);
return v_r_696_;
}
}
uint32_t l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(uint32_t v_idx_697_){
_start:
{
uint32_t v___x_698_; uint32_t v___x_699_; 
v___x_698_ = 4227858432;
v___x_699_ = lean_uint32_lor(v___x_698_, v_idx_697_);
return v___x_699_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_assemblerInternal_0interp(lean_interpreter_value* stack)
{
uint32_t v_idx_697_ = stack[0].m_num;
uint32_t v_res_700_;
v_res_700_ = l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(v_idx_697_);
stack->m_num = v_res_700_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_assemblerInternal___boxed(lean_object* v_idx_701_){
_start:
{
uint32_t v_idx_boxed_702_; uint32_t v_res_703_; lean_object* v_r_704_; 
v_idx_boxed_702_ = lean_unbox_uint32(v_idx_701_);
lean_dec(v_idx_701_);
v_res_703_ = l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(v_idx_boxed_702_);
v_r_704_ = lean_box_uint32(v_res_703_);
return v_r_704_;
}
}
lean_object* l_Lean_Compiler_Bytecode_pushInstr(lean_object* v_code_705_, uint32_t v_instr_706_){
_start:
{
uint8_t v___x_707_; lean_object* v_code_708_; uint32_t v___x_709_; uint32_t v___x_710_; uint8_t v___x_711_; lean_object* v_code_712_; uint32_t v___x_713_; uint32_t v___x_714_; uint8_t v___x_715_; lean_object* v_code_716_; uint32_t v___x_717_; uint32_t v___x_718_; uint8_t v___x_719_; lean_object* v___x_720_; 
v___x_707_ = lean_uint32_to_uint8(v_instr_706_);
v_code_708_ = lean_byte_array_push(v_code_705_, v___x_707_);
v___x_709_ = 8;
v___x_710_ = lean_uint32_shift_right(v_instr_706_, v___x_709_);
v___x_711_ = lean_uint32_to_uint8(v___x_710_);
v_code_712_ = lean_byte_array_push(v_code_708_, v___x_711_);
v___x_713_ = 16;
v___x_714_ = lean_uint32_shift_right(v_instr_706_, v___x_713_);
v___x_715_ = lean_uint32_to_uint8(v___x_714_);
v_code_716_ = lean_byte_array_push(v_code_712_, v___x_715_);
v___x_717_ = 24;
v___x_718_ = lean_uint32_shift_right(v_instr_706_, v___x_717_);
v___x_719_ = lean_uint32_to_uint8(v___x_718_);
v___x_720_ = lean_byte_array_push(v_code_716_, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_pushInstr_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_705_ = stack[0].m_obj;
uint32_t v_instr_706_ = stack[1].m_num;
lean_object* v_res_721_;
v_res_721_ = l_Lean_Compiler_Bytecode_pushInstr(v_code_705_, v_instr_706_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr___boxed(lean_object* v_code_722_, lean_object* v_instr_723_){
_start:
{
uint32_t v_instr_boxed_724_; lean_object* v_res_725_; 
v_instr_boxed_724_ = lean_unbox_uint32(v_instr_723_);
lean_dec(v_instr_723_);
v_res_725_ = l_Lean_Compiler_Bytecode_pushInstr(v_code_722_, v_instr_boxed_724_);
return v_res_725_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(lean_object* v_as_726_, size_t v_i_727_, size_t v_stop_728_, lean_object* v_b_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_eq(v_i_727_, v_stop_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint32_t v___x_732_; lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; 
v___x_731_ = lean_array_uget_borrowed(v_as_726_, v_i_727_);
v___x_732_ = lean_unbox_uint32(v___x_731_);
v___x_733_ = l_Lean_Compiler_Bytecode_pushInstr(v_b_729_, v___x_732_);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_727_, v___x_734_);
v_i_727_ = v___x_735_;
v_b_729_ = v___x_733_;
goto _start;
}
else
{
return v_b_729_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_726_ = stack[0].m_obj;
size_t v_i_727_ = stack[1].m_num;
size_t v_stop_728_ = stack[2].m_num;
lean_object* v_b_729_ = stack[3].m_obj;
lean_object* v_res_737_;
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_as_726_, v_i_727_, v_stop_728_, v_b_729_);
stack->m_obj
 = v_res_737_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0___boxed(lean_object* v_as_738_, lean_object* v_i_739_, lean_object* v_stop_740_, lean_object* v_b_741_){
_start:
{
size_t v_i_boxed_742_; size_t v_stop_boxed_743_; lean_object* v_res_744_; 
v_i_boxed_742_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_stop_boxed_743_ = lean_unbox_usize(v_stop_740_);
lean_dec(v_stop_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_as_738_, v_i_boxed_742_, v_stop_boxed_743_, v_b_741_);
lean_dec_ref(v_as_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble(lean_object* v_instrs_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_746_ = lean_array_get_size(v_instrs_745_);
v___x_747_ = lean_unsigned_to_nat(4u);
v___x_748_ = lean_nat_mul(v___x_746_, v___x_747_);
v___x_749_ = lean_mk_empty_byte_array(v___x_748_);
lean_dec(v___x_748_);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_nat_dec_lt(v___x_750_, v___x_746_);
if (v___x_751_ == 0)
{
return v___x_749_;
}
else
{
uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_le(v___x_746_, v___x_746_);
if (v___x_752_ == 0)
{
if (v___x_751_ == 0)
{
return v___x_749_;
}
else
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_746_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_instrs_745_, v___x_753_, v___x_754_, v___x_749_);
return v___x_755_;
}
}
else
{
size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v___x_756_ = ((size_t)0ULL);
v___x_757_ = lean_usize_of_nat(v___x_746_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_instrs_745_, v___x_756_, v___x_757_, v___x_749_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble___boxed(lean_object* v_instrs_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Compiler_Bytecode_assemble(v_instrs_759_);
lean_dec_ref(v_instrs_759_);
return v_res_760_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_addrToString___boxed__const__1(void){
_start:
{
uint32_t v___x_762_; lean_object* v___x_763_; 
v___x_762_ = 48;
v___x_763_ = lean_box_uint32(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString(lean_object* v_addr_764_){
_start:
{
lean_object* v_addr_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_addr_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_addr_765_ = l_Int_toNat(v_addr_764_);
v___x_766_ = lean_unsigned_to_nat(4u);
v___x_767_ = lean_unsigned_to_nat(16u);
v___x_768_ = l_Nat_toDigits(v___x_767_, v_addr_765_);
v___x_769_ = l_List_lengthTR___redArg(v___x_768_);
v___x_770_ = lean_nat_sub(v___x_766_, v___x_769_);
lean_dec(v___x_769_);
v___x_771_ = l_Lean_Compiler_Bytecode_addrToString___boxed__const__1;
v_addr_772_ = l_List_replicateTR_loop___redArg(v___x_771_, v___x_770_, v___x_768_);
v___x_773_ = ((lean_object*)(l_Lean_Compiler_Bytecode_addrToString___closed__0));
v___x_774_ = lean_string_mk(v_addr_772_);
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
lean_dec_ref(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString___boxed(lean_object* v_addr_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Compiler_Bytecode_addrToString(v_addr_776_);
lean_dec(v_addr_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_Bytecode_Instruction_toString_spec__0(lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = lean_nat_to_int(v_a_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__13(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(33554432u);
v___x_794_ = lean_nat_to_int(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__15(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(128u);
v___x_797_ = lean_nat_to_int(v___x_796_);
return v___x_797_;
}
}
lean_object* l_Lean_Compiler_Bytecode_Instruction_toString(uint32_t v_instr_836_, lean_object* v_pos_837_){
_start:
{
uint32_t v___x_838_; uint32_t v___x_839_; uint32_t v_lo13_840_; uint32_t v___x_841_; uint32_t v___x_842_; uint32_t v___x_843_; uint32_t v_lo8_844_; uint32_t v___x_845_; uint32_t v_mid8_846_; uint32_t v___x_847_; uint32_t v___x_848_; uint32_t v___x_849_; uint32_t v___x_850_; uint32_t v_hi10_851_; uint32_t v___x_852_; uint32_t v___x_853_; uint32_t v_lo18_854_; uint32_t v___x_855_; uint32_t v_hi8_856_; uint32_t v_mid10_857_; uint32_t v_lo10_858_; uint32_t v___x_859_; uint32_t v___x_860_; uint32_t v_hi16_861_; uint32_t v_lo16_862_; uint32_t v___x_863_; uint32_t v___x_864_; uint32_t v_all_865_; uint32_t v___x_866_; uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_838_ = 13;
v___x_839_ = 8191;
v_lo13_840_ = lean_uint32_land(v_instr_836_, v___x_839_);
v___x_841_ = lean_uint32_shift_right(v_instr_836_, v___x_838_);
v___x_842_ = 8;
v___x_843_ = 255;
v_lo8_844_ = lean_uint32_land(v_instr_836_, v___x_843_);
v___x_845_ = lean_uint32_shift_right(v_instr_836_, v___x_842_);
v_mid8_846_ = lean_uint32_land(v___x_845_, v___x_843_);
v___x_847_ = 16;
v___x_848_ = lean_uint32_shift_right(v_instr_836_, v___x_847_);
v___x_849_ = 10;
v___x_850_ = 1023;
v_hi10_851_ = lean_uint32_land(v___x_848_, v___x_850_);
v___x_852_ = 18;
v___x_853_ = 262143;
v_lo18_854_ = lean_uint32_land(v_instr_836_, v___x_853_);
v___x_855_ = lean_uint32_shift_right(v_instr_836_, v___x_852_);
v_hi8_856_ = lean_uint32_land(v___x_855_, v___x_843_);
v_mid10_857_ = lean_uint32_land(v___x_845_, v___x_850_);
v_lo10_858_ = lean_uint32_land(v_instr_836_, v___x_850_);
v___x_859_ = lean_uint32_shift_right(v_instr_836_, v___x_849_);
v___x_860_ = 65535;
v_hi16_861_ = lean_uint32_land(v___x_859_, v___x_860_);
v_lo16_862_ = lean_uint32_land(v_instr_836_, v___x_860_);
v___x_863_ = 26;
v___x_864_ = 67108863;
v_all_865_ = lean_uint32_land(v_instr_836_, v___x_864_);
v___x_866_ = lean_uint32_shift_right(v_instr_836_, v___x_863_);
v___x_867_ = 0;
v___x_868_ = lean_uint32_dec_eq(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
uint32_t v___x_869_; uint32_t v_hi13_870_; uint8_t v___x_871_; 
v___x_869_ = 1;
v_hi13_870_ = lean_uint32_land(v___x_841_, v___x_839_);
v___x_871_ = lean_uint32_dec_eq(v___x_866_, v___x_869_);
if (v___x_871_ == 0)
{
uint32_t v___x_872_; uint8_t v___x_873_; 
v___x_872_ = 2;
v___x_873_ = lean_uint32_dec_eq(v___x_866_, v___x_872_);
if (v___x_873_ == 0)
{
uint32_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = 3;
v___x_875_ = lean_uint32_dec_eq(v___x_866_, v___x_874_);
if (v___x_875_ == 0)
{
uint32_t v___x_876_; uint8_t v___x_877_; 
v___x_876_ = 4;
v___x_877_ = lean_uint32_dec_eq(v___x_866_, v___x_876_);
if (v___x_877_ == 0)
{
uint32_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 5;
v___x_879_ = lean_uint32_dec_eq(v___x_866_, v___x_878_);
if (v___x_879_ == 0)
{
uint32_t v___x_880_; uint8_t v___x_881_; 
v___x_880_ = 6;
v___x_881_ = lean_uint32_dec_eq(v___x_866_, v___x_880_);
if (v___x_881_ == 0)
{
uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_882_ = 7;
v___x_883_ = lean_uint32_dec_eq(v___x_866_, v___x_882_);
if (v___x_883_ == 0)
{
uint8_t v___x_884_; 
v___x_884_ = lean_uint32_dec_eq(v___x_866_, v___x_842_);
if (v___x_884_ == 0)
{
uint32_t v_hi18_885_; uint32_t v___x_886_; uint8_t v___x_887_; 
v_hi18_885_ = lean_uint32_land(v___x_845_, v___x_853_);
v___x_886_ = 9;
v___x_887_ = lean_uint32_dec_eq(v___x_866_, v___x_886_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; 
v___x_888_ = lean_uint32_dec_eq(v___x_866_, v___x_849_);
if (v___x_888_ == 0)
{
uint32_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 11;
v___x_890_ = lean_uint32_dec_eq(v___x_866_, v___x_889_);
if (v___x_890_ == 0)
{
uint32_t v___x_891_; uint8_t v___x_892_; 
v___x_891_ = 12;
v___x_892_ = lean_uint32_dec_eq(v___x_866_, v___x_891_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = lean_uint32_dec_eq(v___x_866_, v___x_838_);
if (v___x_893_ == 0)
{
uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 14;
v___x_895_ = lean_uint32_dec_eq(v___x_866_, v___x_894_);
if (v___x_895_ == 0)
{
uint32_t v___x_896_; uint8_t v___x_897_; 
v___x_896_ = 15;
v___x_897_ = lean_uint32_dec_eq(v___x_866_, v___x_896_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
v___x_898_ = lean_uint32_dec_eq(v___x_866_, v___x_847_);
if (v___x_898_ == 0)
{
uint32_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = 17;
v___x_900_ = lean_uint32_dec_eq(v___x_866_, v___x_899_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
v___x_901_ = lean_uint32_dec_eq(v___x_866_, v___x_852_);
if (v___x_901_ == 0)
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 19;
v___x_903_ = lean_uint32_dec_eq(v___x_866_, v___x_902_);
if (v___x_903_ == 0)
{
uint32_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = 20;
v___x_905_ = lean_uint32_dec_eq(v___x_866_, v___x_904_);
if (v___x_905_ == 0)
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 21;
v___x_907_ = lean_uint32_dec_eq(v___x_866_, v___x_906_);
if (v___x_907_ == 0)
{
uint32_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = 22;
v___x_909_ = lean_uint32_dec_eq(v___x_866_, v___x_908_);
if (v___x_909_ == 0)
{
uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 23;
v___x_911_ = lean_uint32_dec_eq(v___x_866_, v___x_910_);
if (v___x_911_ == 0)
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 24;
v___x_913_ = lean_uint32_dec_eq(v___x_866_, v___x_912_);
if (v___x_913_ == 0)
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 25;
v___x_915_ = lean_uint32_dec_eq(v___x_866_, v___x_914_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; 
v___x_916_ = lean_uint32_dec_eq(v___x_866_, v___x_863_);
if (v___x_916_ == 0)
{
uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = 27;
v___x_918_ = lean_uint32_dec_eq(v___x_866_, v___x_917_);
if (v___x_918_ == 0)
{
uint32_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 28;
v___x_920_ = lean_uint32_dec_eq(v___x_866_, v___x_919_);
if (v___x_920_ == 0)
{
uint32_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = 29;
v___x_922_ = lean_uint32_dec_eq(v___x_866_, v___x_921_);
if (v___x_922_ == 0)
{
uint32_t v___x_923_; uint8_t v___x_924_; 
v___x_923_ = 30;
v___x_924_ = lean_uint32_dec_eq(v___x_866_, v___x_923_);
if (v___x_924_ == 0)
{
uint32_t v___x_925_; uint8_t v___x_926_; 
v___x_925_ = 31;
v___x_926_ = lean_uint32_dec_eq(v___x_866_, v___x_925_);
if (v___x_926_ == 0)
{
uint32_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = 32;
v___x_928_ = lean_uint32_dec_eq(v___x_866_, v___x_927_);
if (v___x_928_ == 0)
{
uint32_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = 33;
v___x_930_ = lean_uint32_dec_eq(v___x_866_, v___x_929_);
if (v___x_930_ == 0)
{
uint32_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = 34;
v___x_932_ = lean_uint32_dec_eq(v___x_866_, v___x_931_);
if (v___x_932_ == 0)
{
uint32_t v___x_933_; uint8_t v___x_934_; 
v___x_933_ = 35;
v___x_934_ = lean_uint32_dec_eq(v___x_866_, v___x_933_);
if (v___x_934_ == 0)
{
uint32_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = 36;
v___x_936_ = lean_uint32_dec_eq(v___x_866_, v___x_935_);
if (v___x_936_ == 0)
{
uint32_t v___x_937_; uint8_t v___x_938_; 
v___x_937_ = 37;
v___x_938_ = lean_uint32_dec_eq(v___x_866_, v___x_937_);
if (v___x_938_ == 0)
{
uint32_t v___x_939_; uint8_t v___x_940_; 
v___x_939_ = 38;
v___x_940_ = lean_uint32_dec_eq(v___x_866_, v___x_939_);
if (v___x_940_ == 0)
{
uint32_t v___x_941_; uint8_t v___x_942_; 
v___x_941_ = 39;
v___x_942_ = lean_uint32_dec_eq(v___x_866_, v___x_941_);
if (v___x_942_ == 0)
{
uint32_t v___x_943_; uint8_t v___x_944_; 
v___x_943_ = 40;
v___x_944_ = lean_uint32_dec_eq(v___x_866_, v___x_943_);
if (v___x_944_ == 0)
{
uint32_t v___x_945_; uint8_t v___x_946_; 
v___x_945_ = 41;
v___x_946_ = lean_uint32_dec_eq(v___x_866_, v___x_945_);
if (v___x_946_ == 0)
{
uint32_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = 42;
v___x_948_ = lean_uint32_dec_eq(v___x_866_, v___x_947_);
if (v___x_948_ == 0)
{
uint32_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = 43;
v___x_950_ = lean_uint32_dec_eq(v___x_866_, v___x_949_);
if (v___x_950_ == 0)
{
uint32_t v___x_951_; uint8_t v___x_952_; 
v___x_951_ = 44;
v___x_952_ = lean_uint32_dec_eq(v___x_866_, v___x_951_);
if (v___x_952_ == 0)
{
uint32_t v___x_953_; uint8_t v___x_954_; 
v___x_953_ = 45;
v___x_954_ = lean_uint32_dec_eq(v___x_866_, v___x_953_);
if (v___x_954_ == 0)
{
uint32_t v___x_955_; uint8_t v___x_956_; 
v___x_955_ = 46;
v___x_956_ = lean_uint32_dec_eq(v___x_866_, v___x_955_);
if (v___x_956_ == 0)
{
uint32_t v___x_957_; uint8_t v___x_958_; 
lean_dec(v_pos_837_);
v___x_957_ = 47;
v___x_958_ = lean_uint32_dec_eq(v___x_866_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_959_ = ((lean_object*)(l_Lean_Compiler_Bytecode_addrToString___closed__0));
v___x_960_ = lean_unsigned_to_nat(32u);
v___x_961_ = lean_uint32_to_nat(v_instr_836_);
v___x_962_ = l_BitVec_toHex(v___x_960_, v___x_961_);
v___x_963_ = lean_string_append(v___x_959_, v___x_962_);
lean_dec_ref(v___x_962_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_964_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__0));
v___x_965_ = lean_uint32_to_nat(v_hi8_856_);
v___x_966_ = l_Nat_reprFast(v___x_965_);
v___x_967_ = lean_string_append(v___x_964_, v___x_966_);
lean_dec_ref(v___x_966_);
v___x_968_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__1));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
v___x_970_ = lean_uint32_to_nat(v_lo18_854_);
v___x_971_ = l_Nat_reprFast(v___x_970_);
v___x_972_ = lean_string_append(v___x_969_, v___x_971_);
lean_dec_ref(v___x_971_);
return v___x_972_;
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_973_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__2));
v___x_974_ = lean_nat_to_int(v_pos_837_);
v___x_975_ = lean_uint32_to_nat(v_all_865_);
v___x_976_ = lean_nat_to_int(v___x_975_);
v___x_977_ = lean_int_add(v___x_974_, v___x_976_);
lean_dec(v___x_976_);
lean_dec(v___x_974_);
v___x_978_ = l_Lean_Compiler_Bytecode_addrToString(v___x_977_);
lean_dec(v___x_977_);
v___x_979_ = lean_string_append(v___x_973_, v___x_978_);
lean_dec_ref(v___x_978_);
return v___x_979_;
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_pos_837_);
v___x_980_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__3));
v___x_981_ = lean_uint32_to_nat(v_lo8_844_);
v___x_982_ = l_Nat_reprFast(v___x_981_);
v___x_983_ = lean_string_append(v___x_980_, v___x_982_);
lean_dec_ref(v___x_982_);
return v___x_983_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_pos_837_);
v___x_984_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__4));
v___x_985_ = lean_uint32_to_nat(v_hi8_856_);
v___x_986_ = l_Nat_reprFast(v___x_985_);
v___x_987_ = lean_string_append(v___x_984_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
v___x_990_ = lean_uint32_to_nat(v_mid10_857_);
v___x_991_ = l_Nat_reprFast(v___x_990_);
v___x_992_ = lean_string_append(v___x_989_, v___x_991_);
lean_dec_ref(v___x_991_);
v___x_993_ = lean_string_append(v___x_992_, v___x_988_);
v___x_994_ = lean_uint32_to_nat(v_lo8_844_);
v___x_995_ = l_Nat_reprFast(v___x_994_);
v___x_996_ = lean_string_append(v___x_993_, v___x_995_);
lean_dec_ref(v___x_995_);
return v___x_996_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_pos_837_);
v___x_997_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__6));
v___x_998_ = lean_uint32_to_nat(v_hi10_851_);
v___x_999_ = l_Nat_reprFast(v___x_998_);
v___x_1000_ = lean_string_append(v___x_997_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
v___x_1003_ = lean_uint32_to_nat(v_mid8_846_);
v___x_1004_ = l_Nat_reprFast(v___x_1003_);
v___x_1005_ = lean_string_append(v___x_1002_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_string_append(v___x_1005_, v___x_1001_);
v___x_1007_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1008_ = l_Nat_reprFast(v___x_1007_);
v___x_1009_ = lean_string_append(v___x_1006_, v___x_1008_);
lean_dec_ref(v___x_1008_);
return v___x_1009_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_pos_837_);
v___x_1010_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__8));
v___x_1011_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1012_ = l_Nat_reprFast(v___x_1011_);
v___x_1013_ = lean_string_append(v___x_1010_, v___x_1012_);
lean_dec_ref(v___x_1012_);
return v___x_1013_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_pos_837_);
v___x_1014_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__9));
v___x_1015_ = lean_uint32_to_nat(v_hi10_851_);
v___x_1016_ = l_Nat_reprFast(v___x_1015_);
v___x_1017_ = lean_string_append(v___x_1014_, v___x_1016_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__10));
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
v___x_1020_ = lean_uint32_to_nat(v_lo16_862_);
v___x_1021_ = l_Nat_reprFast(v___x_1020_);
v___x_1022_ = lean_string_append(v___x_1019_, v___x_1021_);
lean_dec_ref(v___x_1021_);
return v___x_1022_;
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v_pos_837_);
v___x_1023_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__11));
v___x_1024_ = lean_uint32_to_nat(v_hi10_851_);
v___x_1025_ = l_Nat_reprFast(v___x_1024_);
v___x_1026_ = lean_string_append(v___x_1023_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1028_ = lean_string_append(v___x_1026_, v___x_1027_);
v___x_1029_ = lean_uint32_to_nat(v_lo16_862_);
v___x_1030_ = l_Nat_reprFast(v___x_1029_);
v___x_1031_ = lean_string_append(v___x_1028_, v___x_1030_);
lean_dec_ref(v___x_1030_);
return v___x_1031_;
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1032_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__12));
v___x_1033_ = lean_nat_to_int(v_pos_837_);
v___x_1034_ = lean_uint32_to_nat(v_all_865_);
v___x_1035_ = lean_nat_to_int(v___x_1034_);
v___x_1036_ = lean_int_add(v___x_1033_, v___x_1035_);
lean_dec(v___x_1035_);
lean_dec(v___x_1033_);
v___x_1037_ = lean_obj_once(&l_Lean_Compiler_Bytecode_Instruction_toString___closed__13, &l_Lean_Compiler_Bytecode_Instruction_toString___closed__13_once, _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__13);
v___x_1038_ = lean_int_sub(v___x_1036_, v___x_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1038_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1032_, v___x_1039_);
lean_dec_ref(v___x_1039_);
return v___x_1040_;
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1041_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__14));
v___x_1042_ = lean_uint32_to_nat(v_hi8_856_);
v___x_1043_ = l_Nat_reprFast(v___x_1042_);
v___x_1044_ = lean_string_append(v___x_1041_, v___x_1043_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
v___x_1047_ = lean_uint32_to_nat(v_mid10_857_);
v___x_1048_ = l_Nat_reprFast(v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1046_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = lean_string_append(v___x_1049_, v___x_1045_);
v___x_1051_ = lean_nat_to_int(v_pos_837_);
v___x_1052_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1053_ = lean_nat_to_int(v___x_1052_);
v___x_1054_ = lean_int_add(v___x_1051_, v___x_1053_);
lean_dec(v___x_1053_);
lean_dec(v___x_1051_);
v___x_1055_ = lean_obj_once(&l_Lean_Compiler_Bytecode_Instruction_toString___closed__15, &l_Lean_Compiler_Bytecode_Instruction_toString___closed__15_once, _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__15);
v___x_1056_ = lean_int_sub(v___x_1054_, v___x_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1056_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_string_append(v___x_1050_, v___x_1057_);
lean_dec_ref(v___x_1057_);
return v___x_1058_;
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v_pos_837_);
v___x_1059_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__16));
v___x_1060_ = lean_uint32_to_nat(v_all_865_);
v___x_1061_ = l_Nat_reprFast(v___x_1060_);
v___x_1062_ = lean_string_append(v___x_1059_, v___x_1061_);
lean_dec_ref(v___x_1061_);
return v___x_1062_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_pos_837_);
v___x_1063_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__17));
v___x_1064_ = lean_uint32_to_nat(v_hi16_861_);
v___x_1065_ = l_Nat_reprFast(v___x_1064_);
v___x_1066_ = lean_string_append(v___x_1063_, v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1068_ = lean_string_append(v___x_1066_, v___x_1067_);
v___x_1069_ = lean_uint32_to_nat(v_lo10_858_);
v___x_1070_ = l_Nat_reprFast(v___x_1069_);
v___x_1071_ = lean_string_append(v___x_1068_, v___x_1070_);
lean_dec_ref(v___x_1070_);
return v___x_1071_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec(v_pos_837_);
v___x_1072_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__18));
v___x_1073_ = lean_uint32_to_nat(v_hi16_861_);
v___x_1074_ = l_Nat_reprFast(v___x_1073_);
v___x_1075_ = lean_string_append(v___x_1072_, v___x_1074_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
v___x_1078_ = lean_uint32_to_nat(v_lo10_858_);
v___x_1079_ = l_Nat_reprFast(v___x_1078_);
v___x_1080_ = lean_string_append(v___x_1077_, v___x_1079_);
lean_dec_ref(v___x_1079_);
return v___x_1080_;
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v_pos_837_);
v___x_1081_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__19));
v___x_1082_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1083_ = l_Nat_reprFast(v___x_1082_);
v___x_1084_ = lean_string_append(v___x_1081_, v___x_1083_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1086_ = lean_string_append(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1088_ = l_Nat_reprFast(v___x_1087_);
v___x_1089_ = lean_string_append(v___x_1086_, v___x_1088_);
lean_dec_ref(v___x_1088_);
return v___x_1089_;
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_pos_837_);
v___x_1090_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__20));
v___x_1091_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1092_ = l_Nat_reprFast(v___x_1091_);
v___x_1093_ = lean_string_append(v___x_1090_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
v___x_1096_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1097_ = l_Nat_reprFast(v___x_1096_);
v___x_1098_ = lean_string_append(v___x_1095_, v___x_1097_);
lean_dec_ref(v___x_1097_);
return v___x_1098_;
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v_pos_837_);
v___x_1099_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__21));
v___x_1100_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1101_ = l_Nat_reprFast(v___x_1100_);
v___x_1102_ = lean_string_append(v___x_1099_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1106_ = l_Nat_reprFast(v___x_1105_);
v___x_1107_ = lean_string_append(v___x_1104_, v___x_1106_);
lean_dec_ref(v___x_1106_);
return v___x_1107_;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_pos_837_);
v___x_1108_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__22));
v___x_1109_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1110_ = l_Nat_reprFast(v___x_1109_);
v___x_1111_ = lean_string_append(v___x_1108_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1115_ = l_Nat_reprFast(v___x_1114_);
v___x_1116_ = lean_string_append(v___x_1113_, v___x_1115_);
lean_dec_ref(v___x_1115_);
return v___x_1116_;
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec(v_pos_837_);
v___x_1117_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__23));
v___x_1118_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1119_ = l_Nat_reprFast(v___x_1118_);
v___x_1120_ = lean_string_append(v___x_1117_, v___x_1119_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1122_ = lean_string_append(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1124_ = l_Nat_reprFast(v___x_1123_);
v___x_1125_ = lean_string_append(v___x_1122_, v___x_1124_);
lean_dec_ref(v___x_1124_);
return v___x_1125_;
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_pos_837_);
v___x_1126_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__24));
v___x_1127_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1128_ = l_Nat_reprFast(v___x_1127_);
v___x_1129_ = lean_string_append(v___x_1126_, v___x_1128_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1131_ = lean_string_append(v___x_1129_, v___x_1130_);
v___x_1132_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1133_ = l_Nat_reprFast(v___x_1132_);
v___x_1134_ = lean_string_append(v___x_1131_, v___x_1133_);
lean_dec_ref(v___x_1133_);
return v___x_1134_;
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_pos_837_);
v___x_1135_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__25));
v___x_1136_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1137_ = l_Nat_reprFast(v___x_1136_);
v___x_1138_ = lean_string_append(v___x_1135_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___x_1141_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1142_ = l_Nat_reprFast(v___x_1141_);
v___x_1143_ = lean_string_append(v___x_1140_, v___x_1142_);
lean_dec_ref(v___x_1142_);
return v___x_1143_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec(v_pos_837_);
v___x_1144_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__26));
v___x_1145_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1146_ = l_Nat_reprFast(v___x_1145_);
v___x_1147_ = lean_string_append(v___x_1144_, v___x_1146_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1149_ = lean_string_append(v___x_1147_, v___x_1148_);
v___x_1150_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1151_ = l_Nat_reprFast(v___x_1150_);
v___x_1152_ = lean_string_append(v___x_1149_, v___x_1151_);
lean_dec_ref(v___x_1151_);
return v___x_1152_;
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_pos_837_);
v___x_1153_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__27));
v___x_1154_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1155_ = l_Nat_reprFast(v___x_1154_);
v___x_1156_ = lean_string_append(v___x_1153_, v___x_1155_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1158_ = lean_string_append(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1160_ = l_Nat_reprFast(v___x_1159_);
v___x_1161_ = lean_string_append(v___x_1158_, v___x_1160_);
lean_dec_ref(v___x_1160_);
return v___x_1161_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v_pos_837_);
v___x_1162_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__28));
v___x_1163_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1164_ = l_Nat_reprFast(v___x_1163_);
v___x_1165_ = lean_string_append(v___x_1162_, v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1167_ = lean_string_append(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1169_ = l_Nat_reprFast(v___x_1168_);
v___x_1170_ = lean_string_append(v___x_1167_, v___x_1169_);
lean_dec_ref(v___x_1169_);
return v___x_1170_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_pos_837_);
v___x_1171_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__29));
v___x_1172_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1173_ = l_Nat_reprFast(v___x_1172_);
v___x_1174_ = lean_string_append(v___x_1171_, v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1176_ = lean_string_append(v___x_1174_, v___x_1175_);
v___x_1177_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1178_ = l_Nat_reprFast(v___x_1177_);
v___x_1179_ = lean_string_append(v___x_1176_, v___x_1178_);
lean_dec_ref(v___x_1178_);
return v___x_1179_;
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_pos_837_);
v___x_1180_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__30));
v___x_1181_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1182_ = l_Nat_reprFast(v___x_1181_);
v___x_1183_ = lean_string_append(v___x_1180_, v___x_1182_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1185_ = lean_string_append(v___x_1183_, v___x_1184_);
v___x_1186_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1187_ = l_Nat_reprFast(v___x_1186_);
v___x_1188_ = lean_string_append(v___x_1185_, v___x_1187_);
lean_dec_ref(v___x_1187_);
return v___x_1188_;
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v_pos_837_);
v___x_1189_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__31));
v___x_1190_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1191_ = l_Nat_reprFast(v___x_1190_);
v___x_1192_ = lean_string_append(v___x_1189_, v___x_1191_);
lean_dec_ref(v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
v___x_1195_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1196_ = l_Nat_reprFast(v___x_1195_);
v___x_1197_ = lean_string_append(v___x_1194_, v___x_1196_);
lean_dec_ref(v___x_1196_);
return v___x_1197_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_pos_837_);
v___x_1198_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__32));
v___x_1199_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1200_ = l_Nat_reprFast(v___x_1199_);
v___x_1201_ = lean_string_append(v___x_1198_, v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1203_ = lean_string_append(v___x_1201_, v___x_1202_);
v___x_1204_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1205_ = l_Nat_reprFast(v___x_1204_);
v___x_1206_ = lean_string_append(v___x_1203_, v___x_1205_);
lean_dec_ref(v___x_1205_);
return v___x_1206_;
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_pos_837_);
v___x_1207_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__33));
v___x_1208_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1209_ = l_Nat_reprFast(v___x_1208_);
v___x_1210_ = lean_string_append(v___x_1207_, v___x_1209_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1212_ = lean_string_append(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1214_ = l_Nat_reprFast(v___x_1213_);
v___x_1215_ = lean_string_append(v___x_1212_, v___x_1214_);
lean_dec_ref(v___x_1214_);
return v___x_1215_;
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v_pos_837_);
v___x_1216_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__34));
v___x_1217_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1218_ = l_Nat_reprFast(v___x_1217_);
v___x_1219_ = lean_string_append(v___x_1216_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
v___x_1222_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1223_ = l_Nat_reprFast(v___x_1222_);
v___x_1224_ = lean_string_append(v___x_1221_, v___x_1223_);
lean_dec_ref(v___x_1223_);
return v___x_1224_;
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v_pos_837_);
v___x_1225_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__35));
v___x_1226_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1227_ = l_Nat_reprFast(v___x_1226_);
v___x_1228_ = lean_string_append(v___x_1225_, v___x_1227_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1232_ = l_Nat_reprFast(v___x_1231_);
v___x_1233_ = lean_string_append(v___x_1230_, v___x_1232_);
lean_dec_ref(v___x_1232_);
return v___x_1233_;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v_pos_837_);
v___x_1234_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__36));
v___x_1235_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1236_ = l_Nat_reprFast(v___x_1235_);
v___x_1237_ = lean_string_append(v___x_1234_, v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1239_ = lean_string_append(v___x_1237_, v___x_1238_);
v___x_1240_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1241_ = l_Nat_reprFast(v___x_1240_);
v___x_1242_ = lean_string_append(v___x_1239_, v___x_1241_);
lean_dec_ref(v___x_1241_);
return v___x_1242_;
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_pos_837_);
v___x_1243_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__37));
v___x_1244_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1245_ = l_Nat_reprFast(v___x_1244_);
v___x_1246_ = lean_string_append(v___x_1243_, v___x_1245_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1248_ = lean_string_append(v___x_1246_, v___x_1247_);
v___x_1249_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1250_ = l_Nat_reprFast(v___x_1249_);
v___x_1251_ = lean_string_append(v___x_1248_, v___x_1250_);
lean_dec_ref(v___x_1250_);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_pos_837_);
v___x_1252_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__38));
v___x_1253_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1254_ = l_Nat_reprFast(v___x_1253_);
v___x_1255_ = lean_string_append(v___x_1252_, v___x_1254_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1257_ = lean_string_append(v___x_1255_, v___x_1256_);
v___x_1258_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1259_ = l_Nat_reprFast(v___x_1258_);
v___x_1260_ = lean_string_append(v___x_1257_, v___x_1259_);
lean_dec_ref(v___x_1259_);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec(v_pos_837_);
v___x_1261_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__39));
v___x_1262_ = lean_uint32_to_nat(v_hi10_851_);
v___x_1263_ = l_Nat_reprFast(v___x_1262_);
v___x_1264_ = lean_string_append(v___x_1261_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1266_ = lean_string_append(v___x_1264_, v___x_1265_);
v___x_1267_ = lean_uint32_to_nat(v_mid8_846_);
v___x_1268_ = l_Nat_reprFast(v___x_1267_);
v___x_1269_ = lean_string_append(v___x_1266_, v___x_1268_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1271_ = lean_string_append(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1273_ = l_Nat_reprFast(v___x_1272_);
v___x_1274_ = lean_string_append(v___x_1271_, v___x_1273_);
lean_dec_ref(v___x_1273_);
return v___x_1274_;
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec(v_pos_837_);
v___x_1275_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__40));
v___x_1276_ = lean_uint32_to_nat(v_hi10_851_);
v___x_1277_ = l_Nat_reprFast(v___x_1276_);
v___x_1278_ = lean_string_append(v___x_1275_, v___x_1277_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1280_ = lean_string_append(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_uint32_to_nat(v_mid8_846_);
v___x_1282_ = l_Nat_reprFast(v___x_1281_);
v___x_1283_ = lean_string_append(v___x_1280_, v___x_1282_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1285_ = lean_string_append(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1287_ = l_Nat_reprFast(v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1285_, v___x_1287_);
lean_dec_ref(v___x_1287_);
return v___x_1288_;
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v_pos_837_);
v___x_1289_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__41));
v___x_1290_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1291_ = l_Nat_reprFast(v___x_1290_);
v___x_1292_ = lean_string_append(v___x_1289_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1294_ = lean_string_append(v___x_1292_, v___x_1293_);
v___x_1295_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1296_ = l_Nat_reprFast(v___x_1295_);
v___x_1297_ = lean_string_append(v___x_1294_, v___x_1296_);
lean_dec_ref(v___x_1296_);
return v___x_1297_;
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_pos_837_);
v___x_1298_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__42));
v___x_1299_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1300_ = l_Nat_reprFast(v___x_1299_);
v___x_1301_ = lean_string_append(v___x_1298_, v___x_1300_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1303_ = lean_string_append(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1305_ = l_Nat_reprFast(v___x_1304_);
v___x_1306_ = lean_string_append(v___x_1303_, v___x_1305_);
lean_dec_ref(v___x_1305_);
return v___x_1306_;
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_pos_837_);
v___x_1307_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__43));
v___x_1308_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1309_ = l_Nat_reprFast(v___x_1308_);
v___x_1310_ = lean_string_append(v___x_1307_, v___x_1309_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1314_ = l_Nat_reprFast(v___x_1313_);
v___x_1315_ = lean_string_append(v___x_1312_, v___x_1314_);
lean_dec_ref(v___x_1314_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_pos_837_);
v___x_1316_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__44));
v___x_1317_ = lean_uint32_to_nat(v_hi18_885_);
v___x_1318_ = l_Nat_reprFast(v___x_1317_);
v___x_1319_ = lean_string_append(v___x_1316_, v___x_1318_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1323_ = l_Nat_reprFast(v___x_1322_);
v___x_1324_ = lean_string_append(v___x_1321_, v___x_1323_);
lean_dec_ref(v___x_1323_);
return v___x_1324_;
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec(v_pos_837_);
v___x_1325_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__45));
v___x_1326_ = lean_uint32_to_nat(v_hi10_851_);
v___x_1327_ = l_Nat_reprFast(v___x_1326_);
v___x_1328_ = lean_string_append(v___x_1325_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
v___x_1331_ = lean_uint32_to_nat(v_mid8_846_);
v___x_1332_ = l_Nat_reprFast(v___x_1331_);
v___x_1333_ = lean_string_append(v___x_1330_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1335_ = lean_string_append(v___x_1333_, v___x_1334_);
v___x_1336_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1337_ = l_Nat_reprFast(v___x_1336_);
v___x_1338_ = lean_string_append(v___x_1335_, v___x_1337_);
lean_dec_ref(v___x_1337_);
return v___x_1338_;
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec(v_pos_837_);
v___x_1339_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__46));
v___x_1340_ = lean_uint32_to_nat(v_hi10_851_);
v___x_1341_ = l_Nat_reprFast(v___x_1340_);
v___x_1342_ = lean_string_append(v___x_1339_, v___x_1341_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_uint32_to_nat(v_mid8_846_);
v___x_1346_ = l_Nat_reprFast(v___x_1345_);
v___x_1347_ = lean_string_append(v___x_1344_, v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1349_ = lean_string_append(v___x_1347_, v___x_1348_);
v___x_1350_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1351_ = l_Nat_reprFast(v___x_1350_);
v___x_1352_ = lean_string_append(v___x_1349_, v___x_1351_);
lean_dec_ref(v___x_1351_);
return v___x_1352_;
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_pos_837_);
v___x_1353_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__47));
v___x_1354_ = lean_uint32_to_nat(v_hi8_856_);
v___x_1355_ = l_Nat_reprFast(v___x_1354_);
v___x_1356_ = lean_string_append(v___x_1353_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_uint32_to_nat(v_mid10_857_);
v___x_1360_ = l_Nat_reprFast(v___x_1359_);
v___x_1361_ = lean_string_append(v___x_1358_, v___x_1360_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = lean_string_append(v___x_1361_, v___x_1357_);
v___x_1363_ = lean_uint32_to_nat(v_lo8_844_);
v___x_1364_ = l_Nat_reprFast(v___x_1363_);
v___x_1365_ = lean_string_append(v___x_1362_, v___x_1364_);
lean_dec_ref(v___x_1364_);
return v___x_1365_;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v_pos_837_);
v___x_1366_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__48));
v___x_1367_ = lean_uint32_to_nat(v_hi13_870_);
v___x_1368_ = l_Nat_reprFast(v___x_1367_);
v___x_1369_ = lean_string_append(v___x_1366_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
v___x_1372_ = lean_uint32_to_nat(v_lo13_840_);
v___x_1373_ = l_Nat_reprFast(v___x_1372_);
v___x_1374_ = lean_string_append(v___x_1371_, v___x_1373_);
lean_dec_ref(v___x_1373_);
return v___x_1374_;
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_pos_837_);
v___x_1375_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__49));
v___x_1376_ = lean_uint32_to_nat(v_all_865_);
v___x_1377_ = l_Nat_reprFast(v___x_1376_);
v___x_1378_ = lean_string_append(v___x_1375_, v___x_1377_);
lean_dec_ref(v___x_1377_);
return v___x_1378_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v_pos_837_);
v___x_1379_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__50));
v___x_1380_ = lean_uint32_to_nat(v_all_865_);
v___x_1381_ = l_Nat_reprFast(v___x_1380_);
v___x_1382_ = lean_string_append(v___x_1379_, v___x_1381_);
lean_dec_ref(v___x_1381_);
return v___x_1382_;
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v_pos_837_);
v___x_1383_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__51));
v___x_1384_ = lean_uint32_to_nat(v_all_865_);
v___x_1385_ = l_Nat_reprFast(v___x_1384_);
v___x_1386_ = lean_string_append(v___x_1383_, v___x_1385_);
lean_dec_ref(v___x_1385_);
return v___x_1386_;
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec(v_pos_837_);
v___x_1387_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__52));
v___x_1388_ = lean_uint32_to_nat(v_hi13_870_);
v___x_1389_ = l_Nat_reprFast(v___x_1388_);
v___x_1390_ = lean_string_append(v___x_1387_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_uint32_to_nat(v_lo13_840_);
v___x_1394_ = l_Nat_reprFast(v___x_1393_);
v___x_1395_ = lean_string_append(v___x_1392_, v___x_1394_);
lean_dec_ref(v___x_1394_);
return v___x_1395_;
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_pos_837_);
v___x_1396_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__53));
v___x_1397_ = lean_uint32_to_nat(v_hi8_856_);
v___x_1398_ = l_Nat_reprFast(v___x_1397_);
v___x_1399_ = lean_string_append(v___x_1396_, v___x_1398_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
v___x_1402_ = lean_uint32_to_nat(v_lo18_854_);
v___x_1403_ = l_Nat_reprFast(v___x_1402_);
v___x_1404_ = lean_string_append(v___x_1401_, v___x_1403_);
lean_dec_ref(v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_Instruction_toString_0interp(lean_interpreter_value* stack)
{
uint32_t v_instr_836_ = stack[0].m_num;
lean_object* v_pos_837_ = stack[1].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_Compiler_Bytecode_Instruction_toString(v_instr_836_, v_pos_837_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___boxed(lean_object* v_instr_1406_, lean_object* v_pos_1407_){
_start:
{
uint32_t v_instr_boxed_1408_; lean_object* v_res_1409_; 
v_instr_boxed_1408_ = lean_unbox_uint32(v_instr_1406_);
lean_dec(v_instr_1406_);
v_res_1409_ = l_Lean_Compiler_Bytecode_Instruction_toString(v_instr_boxed_1408_, v_pos_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(lean_object* v_upperBound_1412_, lean_object* v___x_1413_, lean_object* v_a_1414_, lean_object* v_b_1415_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_lt(v_a_1414_, v_upperBound_1412_);
if (v___x_1416_ == 0)
{
lean_dec(v_a_1414_);
return v_b_1415_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; uint32_t v___x_1431_; uint32_t v___x_1432_; uint32_t v___x_1433_; uint32_t v___x_1434_; uint32_t v___x_1435_; uint32_t v___x_1436_; uint32_t v___x_1437_; uint32_t v___x_1438_; uint32_t v___x_1439_; uint32_t v___x_1440_; uint32_t v___x_1441_; uint32_t v___x_1442_; uint32_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1417_ = lean_unsigned_to_nat(4u);
lean_inc(v_a_1414_);
v___x_1418_ = lean_nat_to_int(v_a_1414_);
v___x_1419_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1418_);
lean_dec(v___x_1418_);
v___x_1420_ = lean_nat_mul(v_a_1414_, v___x_1417_);
v___x_1421_ = lean_byte_array_fget(v___x_1413_, v___x_1420_);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v___x_1420_, v___x_1422_);
v___x_1424_ = lean_byte_array_fget(v___x_1413_, v___x_1423_);
lean_dec(v___x_1423_);
v___x_1425_ = lean_unsigned_to_nat(2u);
v___x_1426_ = lean_nat_add(v___x_1420_, v___x_1425_);
v___x_1427_ = lean_byte_array_fget(v___x_1413_, v___x_1426_);
lean_dec(v___x_1426_);
v___x_1428_ = lean_unsigned_to_nat(3u);
v___x_1429_ = lean_nat_add(v___x_1420_, v___x_1428_);
lean_dec(v___x_1420_);
v___x_1430_ = lean_byte_array_fget(v___x_1413_, v___x_1429_);
lean_dec(v___x_1429_);
v___x_1431_ = lean_uint8_to_uint32(v___x_1421_);
v___x_1432_ = lean_uint8_to_uint32(v___x_1424_);
v___x_1433_ = 8;
v___x_1434_ = lean_uint32_shift_left(v___x_1432_, v___x_1433_);
v___x_1435_ = lean_uint32_lor(v___x_1431_, v___x_1434_);
v___x_1436_ = lean_uint8_to_uint32(v___x_1427_);
v___x_1437_ = 16;
v___x_1438_ = lean_uint32_shift_left(v___x_1436_, v___x_1437_);
v___x_1439_ = lean_uint32_lor(v___x_1435_, v___x_1438_);
v___x_1440_ = lean_uint8_to_uint32(v___x_1430_);
v___x_1441_ = 24;
v___x_1442_ = lean_uint32_shift_left(v___x_1440_, v___x_1441_);
v___x_1443_ = lean_uint32_lor(v___x_1439_, v___x_1442_);
v___x_1444_ = lean_string_append(v_b_1415_, v___x_1419_);
lean_dec_ref(v___x_1419_);
v___x_1445_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0));
v___x_1446_ = lean_string_append(v___x_1444_, v___x_1445_);
v___x_1447_ = lean_nat_add(v_a_1414_, v___x_1422_);
lean_dec(v_a_1414_);
lean_inc(v___x_1447_);
v___x_1448_ = l_Lean_Compiler_Bytecode_Instruction_toString(v___x_1443_, v___x_1447_);
v___x_1449_ = lean_string_append(v___x_1446_, v___x_1448_);
lean_dec_ref(v___x_1448_);
v___x_1450_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1));
v___x_1451_ = lean_string_append(v___x_1449_, v___x_1450_);
v_a_1414_ = v___x_1447_;
v_b_1415_ = v___x_1451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1453_, lean_object* v___x_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(v_upperBound_1453_, v___x_1454_, v_a_1455_, v_b_1456_);
lean_dec_ref(v___x_1454_);
lean_dec(v_upperBound_1453_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(lean_object* v_upperBound_1458_, lean_object* v___x_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_nat_dec_lt(v_a_1460_, v_upperBound_1458_);
if (v___x_1462_ == 0)
{
lean_dec(v_a_1460_);
return v_b_1461_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; uint32_t v___x_1477_; uint32_t v___x_1478_; uint32_t v___x_1479_; uint32_t v___x_1480_; uint32_t v___x_1481_; uint32_t v___x_1482_; uint32_t v___x_1483_; uint32_t v___x_1484_; uint32_t v___x_1485_; uint32_t v___x_1486_; uint32_t v___x_1487_; uint32_t v___x_1488_; uint32_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1463_ = lean_unsigned_to_nat(4u);
lean_inc(v_a_1460_);
v___x_1464_ = lean_nat_to_int(v_a_1460_);
v___x_1465_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1464_);
lean_dec(v___x_1464_);
v___x_1466_ = lean_nat_mul(v_a_1460_, v___x_1463_);
v___x_1467_ = lean_byte_array_fget(v___x_1459_, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v___x_1466_, v___x_1468_);
v___x_1470_ = lean_byte_array_fget(v___x_1459_, v___x_1469_);
lean_dec(v___x_1469_);
v___x_1471_ = lean_unsigned_to_nat(2u);
v___x_1472_ = lean_nat_add(v___x_1466_, v___x_1471_);
v___x_1473_ = lean_byte_array_fget(v___x_1459_, v___x_1472_);
lean_dec(v___x_1472_);
v___x_1474_ = lean_unsigned_to_nat(3u);
v___x_1475_ = lean_nat_add(v___x_1466_, v___x_1474_);
lean_dec(v___x_1466_);
v___x_1476_ = lean_byte_array_fget(v___x_1459_, v___x_1475_);
lean_dec(v___x_1475_);
v___x_1477_ = lean_uint8_to_uint32(v___x_1467_);
v___x_1478_ = lean_uint8_to_uint32(v___x_1470_);
v___x_1479_ = 8;
v___x_1480_ = lean_uint32_shift_left(v___x_1478_, v___x_1479_);
v___x_1481_ = lean_uint32_lor(v___x_1477_, v___x_1480_);
v___x_1482_ = lean_uint8_to_uint32(v___x_1473_);
v___x_1483_ = 16;
v___x_1484_ = lean_uint32_shift_left(v___x_1482_, v___x_1483_);
v___x_1485_ = lean_uint32_lor(v___x_1481_, v___x_1484_);
v___x_1486_ = lean_uint8_to_uint32(v___x_1476_);
v___x_1487_ = 24;
v___x_1488_ = lean_uint32_shift_left(v___x_1486_, v___x_1487_);
v___x_1489_ = lean_uint32_lor(v___x_1485_, v___x_1488_);
v___x_1490_ = lean_string_append(v_b_1461_, v___x_1465_);
lean_dec_ref(v___x_1465_);
v___x_1491_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0));
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
v___x_1493_ = lean_nat_add(v_a_1460_, v___x_1468_);
lean_dec(v_a_1460_);
lean_inc(v___x_1493_);
v___x_1494_ = l_Lean_Compiler_Bytecode_Instruction_toString(v___x_1489_, v___x_1493_);
v___x_1495_ = lean_string_append(v___x_1492_, v___x_1494_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1));
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
v___x_1498_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(v_upperBound_1458_, v___x_1459_, v___x_1493_, v___x_1497_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg___boxed(lean_object* v_upperBound_1499_, lean_object* v___x_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(v_upperBound_1499_, v___x_1500_, v_a_1501_, v_b_1502_);
lean_dec_ref(v___x_1500_);
lean_dec(v_upperBound_1499_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(lean_object* v_upperBound_1505_, lean_object* v___x_1506_, lean_object* v_a_1507_, lean_object* v_b_1508_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_lt(v_a_1507_, v_upperBound_1505_);
if (v___x_1509_ == 0)
{
lean_dec(v_a_1507_);
return v_b_1508_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1510_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0));
v___x_1511_ = lean_string_append(v_b_1508_, v___x_1510_);
lean_inc(v_a_1507_);
v___x_1512_ = l_Nat_reprFast(v_a_1507_);
v___x_1513_ = lean_string_append(v___x_1511_, v___x_1512_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0));
v___x_1515_ = lean_string_append(v___x_1513_, v___x_1514_);
v___x_1516_ = lean_array_fget_borrowed(v___x_1506_, v_a_1507_);
lean_inc(v___x_1516_);
v___x_1517_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1516_, v___x_1509_);
v___x_1518_ = lean_string_append(v___x_1515_, v___x_1517_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1));
v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_nat_add(v_a_1507_, v___x_1521_);
lean_dec(v_a_1507_);
v_a_1507_ = v___x_1522_;
v_b_1508_ = v___x_1520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___boxed(lean_object* v_upperBound_1524_, lean_object* v___x_1525_, lean_object* v_a_1526_, lean_object* v_b_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(v_upperBound_1524_, v___x_1525_, v_a_1526_, v_b_1527_);
lean_dec_ref(v___x_1525_);
lean_dec(v_upperBound_1524_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* lean_bytecode_disass(lean_object* v_code_1536_){
_start:
{
lean_object* v_name_1537_; lean_object* v_code_1538_; lean_object* v_stackReserved_1539_; lean_object* v_stackSpace_1540_; lean_object* v_symbols_1541_; lean_object* v_arity_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_sz_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_str_1564_; lean_object* v___x_1565_; lean_object* v_str_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_name_1537_ = lean_ctor_get(v_code_1536_, 0);
lean_inc(v_name_1537_);
v_code_1538_ = lean_ctor_get(v_code_1536_, 1);
lean_inc_ref(v_code_1538_);
v_stackReserved_1539_ = lean_ctor_get(v_code_1536_, 2);
lean_inc(v_stackReserved_1539_);
v_stackSpace_1540_ = lean_ctor_get(v_code_1536_, 3);
lean_inc(v_stackSpace_1540_);
v_symbols_1541_ = lean_ctor_get(v_code_1536_, 4);
lean_inc_ref(v_symbols_1541_);
v_arity_1542_ = lean_ctor_get(v_code_1536_, 6);
lean_inc(v_arity_1542_);
lean_dec_ref(v_code_1536_);
v___x_1543_ = lean_byte_array_size(v_code_1538_);
v___x_1544_ = lean_unsigned_to_nat(2u);
v_sz_1545_ = lean_nat_shiftr(v___x_1543_, v___x_1544_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__0));
v___x_1548_ = 1;
v___x_1549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1537_, v___x_1548_);
v___x_1550_ = lean_string_append(v___x_1547_, v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__1));
v___x_1552_ = lean_string_append(v___x_1550_, v___x_1551_);
v___x_1553_ = l_Nat_reprFast(v_arity_1542_);
v___x_1554_ = lean_string_append(v___x_1552_, v___x_1553_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__2));
v___x_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
v___x_1557_ = l_Nat_reprFast(v_stackSpace_1540_);
v___x_1558_ = lean_string_append(v___x_1556_, v___x_1557_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__3));
v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
v___x_1561_ = l_Nat_reprFast(v_stackReserved_1539_);
v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__4));
v_str_1564_ = lean_string_append(v___x_1562_, v___x_1563_);
v___x_1565_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__5));
v_str_1566_ = lean_string_append(v_str_1564_, v___x_1565_);
v___x_1567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(v_sz_1545_, v_code_1538_, v___x_1546_, v_str_1566_);
lean_dec_ref(v_code_1538_);
lean_dec(v_sz_1545_);
v___x_1568_ = lean_array_get_size(v_symbols_1541_);
v___x_1569_ = lean_nat_dec_eq(v___x_1568_, v___x_1546_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__6));
v___x_1571_ = lean_string_append(v___x_1567_, v___x_1570_);
v___x_1572_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(v___x_1568_, v_symbols_1541_, v___x_1546_, v___x_1571_);
lean_dec_ref(v_symbols_1541_);
return v___x_1572_;
}
else
{
lean_dec_ref(v_symbols_1541_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0(lean_object* v_upperBound_1573_, lean_object* v___x_1574_, lean_object* v_inst_1575_, lean_object* v_R_1576_, lean_object* v_a_1577_, lean_object* v_b_1578_, lean_object* v_c_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(v_upperBound_1573_, v___x_1574_, v_a_1577_, v_b_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___boxed(lean_object* v_upperBound_1581_, lean_object* v___x_1582_, lean_object* v_inst_1583_, lean_object* v_R_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v_c_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0(v_upperBound_1581_, v___x_1582_, v_inst_1583_, v_R_1584_, v_a_1585_, v_b_1586_, v_c_1587_);
lean_dec_ref(v___x_1582_);
lean_dec(v_upperBound_1581_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1(lean_object* v_upperBound_1589_, lean_object* v___x_1590_, lean_object* v_inst_1591_, lean_object* v_R_1592_, lean_object* v_a_1593_, lean_object* v_b_1594_, lean_object* v_c_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(v_upperBound_1589_, v___x_1590_, v_a_1593_, v_b_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___boxed(lean_object* v_upperBound_1597_, lean_object* v___x_1598_, lean_object* v_inst_1599_, lean_object* v_R_1600_, lean_object* v_a_1601_, lean_object* v_b_1602_, lean_object* v_c_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1(v_upperBound_1597_, v___x_1598_, v_inst_1599_, v_R_1600_, v_a_1601_, v_b_1602_, v_c_1603_);
lean_dec_ref(v___x_1598_);
lean_dec(v_upperBound_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1(lean_object* v_upperBound_1605_, lean_object* v___x_1606_, lean_object* v_inst_1607_, lean_object* v_R_1608_, lean_object* v_a_1609_, lean_object* v_b_1610_, lean_object* v_c_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(v_upperBound_1605_, v___x_1606_, v_a_1609_, v_b_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___boxed(lean_object* v_upperBound_1613_, lean_object* v___x_1614_, lean_object* v_inst_1615_, lean_object* v_R_1616_, lean_object* v_a_1617_, lean_object* v_b_1618_, lean_object* v_c_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1(v_upperBound_1613_, v___x_1614_, v_inst_1615_, v_R_1616_, v_a_1617_, v_b_1618_, v_c_1619_);
lean_dec_ref(v___x_1614_);
lean_dec(v_upperBound_1613_);
return v_res_1620_;
}
}
lean_object* runtime_initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_Bytecode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_Bytecode_instInhabitedInstruction_default = _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction_default();
l_Lean_Compiler_Bytecode_instInhabitedInstruction = _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction();
l_Lean_Compiler_Bytecode_maxUConst = _init_l_Lean_Compiler_Bytecode_maxUConst();
lean_mark_persistent(l_Lean_Compiler_Bytecode_maxUConst);
l_Lean_Compiler_Bytecode_maxNConst = _init_l_Lean_Compiler_Bytecode_maxNConst();
lean_mark_persistent(l_Lean_Compiler_Bytecode_maxNConst);
l_Lean_Compiler_Bytecode_Instruction_nojump = _init_l_Lean_Compiler_Bytecode_Instruction_nojump();
l_Lean_Compiler_Bytecode_addrToString___boxed__const__1 = _init_l_Lean_Compiler_Bytecode_addrToString___boxed__const__1();
lean_mark_persistent(l_Lean_Compiler_Bytecode_addrToString___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_Bytecode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Bytecode_Instruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Bytecode_Instruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Bytecode_Instruction(builtin);
}
#ifdef __cplusplus
}
#endif
