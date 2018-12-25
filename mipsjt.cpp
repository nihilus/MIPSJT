/*
 *
 * PowerPC Jump Tables analysis Module
 *
 * The PowerPC processor module in IDA Pro 4.8 does not handle jump tables.
 * This module will try to find the jump tables and tell IDA about them
 * so the function analysis can be as good as possible.
 *
 *
 * Copyright (C) Youness Alaoui (KaKaRoTo)
 *
 * This software is distributed under the terms of the GNU General Public
 * License ("GPL") version 3, as published by the Free Software Foundation.
 *
 * This payload is a modified version of the original PSJailbreak's payload.
 * The people behing PSJailbrak are the original authors and copyright holders
 * of the code they wrote.
 */


#include <ida.hpp>
#include <idp.hpp>
#include <name.hpp>
#include <bytes.hpp>
#include <loader.hpp>
#include <allins.hpp>
#include <kernwin.hpp>
#include <problems.hpp>
#include <auto.hpp>
#include <ua.hpp>
#include <offset.hpp>

//#define JUMP_DEBUG
#include "../../module/jptcmn.cpp"


#define MIPSJT_VERSION	"v0.2"

qstring g_mnem;
qstring g_opnd_s0;
qstring g_opnd_s1;
qstring g_opnd_s2;

struct mips_jump_pattern_t : public jump_pattern_t
{
  mips_jump_pattern_t(switch_info_t *_si, const char *_roots, const char (*_depends)[2])
    : jump_pattern_t(_si, _roots, _depends) {}
  eavec_t extra_insn_eas; // extra insns used to calculate values
                          // (discovered by find_ldr_value_ex)
  virtual void mark_switch_insns(int /*last*/, int /*first = 1*/)
  {
    // in addition to the regular insns discovered by the pattern matcher, mark
    // the insns found by find_ldr_value_ex()
    /*jump_pattern_t::mark_switch_insns(last, first);
    for ( eavec_t::iterator p = extra_insn_eas.begin(); p != extra_insn_eas.end(); ++p )
      mark_switch_insn(*p);*/
  }
};

//----------------------------------------------------------------------
// ARCompact ldb/ldw/ld switch
// 7      sub     Ra, Ra, #minv (optional)
// 6      cmp     Ra, #size
// 5      bls     L3
// 4      bcs|bhi default | b default
// 3  L3: add     Rtbl, pcl, #imm
// 2      ldb.x   Rb, [Rtbl,Ra]
// 1      add1    Rc, Rtbl, Rb
// 0      j       [Rc]
//jt      DCB bytes...
//
// 0 -> 1 -> 2 -> 3
//             -> 6 -> 7
// 4 -> 5 -> 6 -> 7

static const char root1[] = { 1, 4, 0 };
static const char depend1[][2] =
{
  { 1 },        // 0
  { 2 },        // 1
  { 3, 6 },     // 2
  { 0 },        // 3
  { 5 },        // 4
  { 6 },        // 5
  { -7 },       // 6
  { 0 },        // 7 optional
};

class jump_pattern1_t : public mips_jump_pattern_t
{
protected:
  enum { rA=1, rB, rC, rTbl };
  jump_pattern1_t(switch_info_t *_si, const char *_roots, const char (*_depends)[2])
    : mips_jump_pattern_t(_si, _roots, _depends)
  {
    allow_noflows = false;
  }
public:
  jump_pattern1_t(switch_info_t *_si) : mips_jump_pattern_t(_si, root1, depend1)
  {
    allow_noflows = false;
  }
  virtual bool jpi7(void); //     sub     Ra, Ra, #minv (optional)
  virtual bool jpi6(void); //     cmp     Ra, #size
  virtual bool jpi5(void); //     bls     L3
  virtual bool jpi4(void); //     bcs|bhi default | b default
  virtual bool jpi3(void); // L3: add     Rtbl, pcl, #imm
  virtual bool jpi2(void); //     ldb.x   Rb, [Rtbl,Ra]
  virtual bool jpi1(void); //     add1    Rc, Rtbl, Rb (optional)
  virtual bool jpi0(void); //     j       [Rc]
  // bool check_switch_ldr(bool is_ldrb);
  bool _jpi4(int n);
  bool _jpi5(int numins);
  bool _jpi6(int skip1, int skip2); // cmp Ra, #size | br.nc ra, #size, default
  bool handle_mov();
  bool is_branch_to(ea_t addr_to);
  virtual bool start_tree(ea_t, int n)
  {
    if ( n != 1 )
      allow_farrefs = false;
    return true;
  }
};

//----------------------------------------------------------------------
bool jump_pattern1_t::is_branch_to(ea_t addr_to)
{
  return insn.itype == MIPS_b
      && insn.Op1.addr == addr_to;
}

//----------------------------------------------------------------------
bool jump_pattern1_t::handle_mov(void)
{
  if ( insn.itype != MIPS_mov && insn.itype != MIPS_ld )
    return false;
  if ( insn.Op1.type != o_reg )
    return false;
  // we handle only registers and stkvars
  if ( (insn.Op2.type != o_displ || insn.Op2.phrase != 29)
    && insn.Op2.type != o_reg )
  {
    return false;
  }
  return mov_set(insn.Op1.reg, insn.Op2);
}

bool jump_pattern1_t::jpi7(void) // sub Ra, Ra, #minv (optional)
{
  if ( insn.itype != MIPS_sub
    || spoiled[rA]
    || !insn.Op1.is_reg(r[rA]) )
  {
    return false;
  }

  if ( insn.Op2.type == o_reg && insn.Op3.type == o_imm )
  {
    si->lowcase = insn.Op3.value;
    si->set_expr(insn.Op2.reg, insn.Op2.dtype);
  }
  else
  {
    if ( insn.Op2.type != o_imm )
      return false;
    si->lowcase = insn.Op2.value;
    si->startea = insn.ea;
  }

  // sometimes there is another SUB Ra, Rx, #minv2
  // just before the first SUB
  /*
  insn_t insn1;
  if ( decode_prev_insn(&insn1, insn.ea) != BADADDR
    && insn1.itype == MIPS_sub
    && insn1.Op1.is_reg(r[rA])
    && insn1.Op2.type == o_reg
    && insn1.Op3.type == o_imm )
  {
    si->lowcase += insn1.Op3.value;
    si->set_expr(insn1.Op2.reg, insn1.Op2.dtype);
    r[rA] = insn1.Op2.reg;
    si->startea = insn1.ea;
  } */
  return true;
}

bool jump_pattern1_t::_jpi6(int skip1, int skip2) // cmp Ra, #size | br.nc ra, #size, default
{
  if ((insn.itype != MIPS_cmp && insn.itype != MIPS_and)
    || r[rA] == -1
    || (r[rA] != r[rB] && spoiled[rA])
     )
  {
    // br.nc ra, #size, default
    if (spoiled[rA]
      || !insn.Op1.is_reg(r[rA])
      || insn.Op2.type != o_imm
   		 )
      return false;

    si->ncases = ushort(insn.Op2.value);
    si->set_expr(insn.Op1.reg, insn.Op1.dtype);
    si->startea = insn.ea;
    si->defjump = insn.Op3.addr;
    if ( skip1 != -1 )
      skip[skip1] = true;
    if ( skip2 != -1 )
      skip[skip2] = true;
    return true;
  }

  op_t &expop = insn.Op1;
  if ( insn.itype == MIPS_cmp )
  {
    if ( insn.Op2.type == o_imm )
      si->ncases = ushort(insn.Op2.value);
    /*else if ( insn.Op2.type == o_reg )
    {
      // cmp Ra, Rx
      uval_t value;
      if ( !find_ldr_value(insn, insn.ea, insn.Op2.reg, &value) )
        return false;
      si->ncases = (ushort)value;
    }*/
    else
      return false;
  }
  else
  {
    ushort n;
    if ( insn.Op2.type == o_reg && insn.Op3.type == o_imm )        // ANDS Ra, Rb, #3
    {
      expop = insn.Op2;
      n = ushort(insn.Op3.value);
    }
    else if ( insn.Op2.type == o_imm && insn.Op3.type == o_void )  // ANDS Ra, #3
    {
      n = ushort(insn.Op2.value);
    }
    else
    {
      return false;
    }
    // check that n+1 is a power of 2
    if ( n & (n+1) )
      return false;
    si->ncases = n+1;
  }
  si->set_expr(expop.reg, expop.dtype);
  si->startea = insn.ea;
  return true;
}

bool jump_pattern1_t::jpi6() // cmp Ra, #size | br.nc ra, #size, default
{
  return _jpi6(5, 4);
}

bool jump_pattern1_t::_jpi5(int) // bls L3
{
  if ( insn.itype != MIPS_b )
    return false;
  if ( insn.Op1.addr <= insn.ea )
    return false;
  /*if ( cond(insn) == cLS )
    si->ncases++;*/
  return true;
}

bool jump_pattern1_t::jpi5(void)
{
  return _jpi5(3);
}

bool jump_pattern1_t::_jpi4(int n) // b default | bhi     default
{
  // allow_noflows = true;
  if ( insn.itype != MIPS_b )
    return false;

  
  if (insn.Op1.addr <= eas[3] )
  {
    // we have BLS to the switch instruction
    // followed by B default
    insn_t insn1;
    bool ok = decode_insn(&insn1, insn.ea + insn.size) > 0 /*&& cond(insn) == cAL && _jpi4(n)*/;
    if ( ok )
    {
      if (insn1.itype == MIPS_b ) // b default
      if (insn1.itype == MIPS_b ) // b default
        si->defjump = insn1.Op1.addr;
      else
        si->defjump = insn1.ip;
      skip[n] = true;
    }
    return ok;
  }

  ea_t jump_ip;
  /*if ( insn.itype == MIPS_br )
  {
    if ( !find_ldr_value(insn, insn.ea, insn.Op1.reg, &jump_ip) )
      return false;
    jump_ip &= ~1;
  }
  else*/
  {
    jump_ip = insn.Op1.addr;
  }
  si->defjump = jump_ip;
  return true;
}

bool jump_pattern1_t::jpi4(void) { return _jpi4(5); }

bool jump_pattern1_t::jpi3(void) // add Rtbl, pcl, #imm
{
  if ( insn.itype != MIPS_add
    || spoiled[rTbl]
    || !insn.Op1.is_reg(r[rTbl])
    || insn.Op3.type != o_imm )
  {
    return false;
  }
  ea_t pcval = insn.ip & ~3;
  si->jumps = pcval + insn.Op3.value;
  si->flags |= (si->defjump == BADADDR ? 0 : SWI_DEFAULT) | SWI_ELBASE;
  // si->set_jtable_element_size(jtt == JT_ARM_LDRB ? 1 : 2);
  si->elbase = si->jumps;
  return true;
}

// ldb.x   Rb, [Rtbl,Ra]
// ldw.x.as  Rb, [Rtbl,Ra]
// ld.as   Rb, [Rtbl,Ra]
bool jump_pattern1_t::jpi2()
{
  if ( eas[1] == BADADDR ) // add1 Rc, Rtbl, Rb was missing
    r[rB] = r[rC];

  if ( insn.itype != MIPS_ld
    || spoiled[rB]
    || !insn.Op1.is_reg(r[rB])
    || insn.Op2.type != o_phrase
    || insn.Op2.reg != r[rTbl] )
  {
    return false;
  }

  return true;
}

bool jump_pattern1_t::jpi1(void) // add1    Rc, Rtbl, Rb
{
  if (!spoiled[rC]
    && insn.Op1.is_reg(r[rC]) )
  {
    if ( (insn.itype == MIPS_add)
      && insn.Op2.type == o_reg
      && insn.Op3.type == o_reg )
    {
      r[rTbl] = insn.Op2.reg;
      r[rB]   = insn.Op3.reg;
      return true;
    }
  }
  return false;
}

bool jump_pattern1_t::jpi0(void) // j [Rc]
{
  if (insn.itype != MIPS_j )
    return false;

  r[rC] = insn.Op1.reg;
  return true;
}

//----------------------------------------------------------------------
// Absolute offsets
// 5      sub     Ra, Ra, #minv (optional)
// 4      cmp     Ra, #size               | br.nc ra, #size, default
// 3      bls     L3
// 2      bcs|bhi default | b default
// 1  L3: ld.as   Rb, [#addr,Ra]
// 0      j       [Rb]
//jt      DCB bytes...
//
// 0 -> 1 -> 4 -> 5
// 2 -> 3 -> 4 -> 5

static const char root2[] = { 1, 2, 0 };
static const char depend2[][2] =
{
  { 1 },        // 0
  { 4 },        // 1
  { 3 },        // 2
  { 4 },        // 3
  { -5 },       // 4
  { 0 },        // 5 optional
};

class jump_pattern2_t : public jump_pattern1_t
{
protected:
  jump_pattern2_t(switch_info_t *_si, const char *_roots, const char (*_depends)[2])
    : jump_pattern1_t(_si, _roots, _depends)
  {
  }
public:
  jump_pattern2_t(switch_info_t *_si) : jump_pattern1_t(_si, root2, depend2)
  {
  }
  virtual bool jpi5(void)  //     sub     Ra, Ra, #minv (optional)
  {
    return jump_pattern1_t::jpi7();
  }
  virtual bool jpi4(void);  //     cmp     Ra, #size
  virtual bool jpi3(void)   //     bls     L3
  {
    return _jpi5(1);
  }
  virtual bool jpi2(void)  //     bcs|bhi default | b default
  {
    return _jpi4(3);
  }
  virtual bool jpi1(void); //     ld.as   Rc, [#table,Ra]
  // virtual bool jpi0(void)  //     j       [Rc]
  // bool check_switch_ldr(bool is_ldrb);
};

bool jump_pattern2_t::jpi4(void)
{
  return jump_pattern1_t::_jpi6(2, 3);
}

// ld.as   Rc, [#tbl,Ra]
bool jump_pattern2_t::jpi1()
{
  if ( insn.itype != MIPS_ld
    || spoiled[rC]
    || !insn.Op1.is_reg(r[rC])
    || insn.Op2.type != o_displ)
  {
    return false;
  }

  si->set_jtable_element_size(4);

  si->jumps = insn.Op2.addr;
  // si->flags |= (si->defjump == BADADDR ? 0 : SWI_DEFAULT);
  // si->set_jtable_element_size(jtt == JT_ARM_LDRB ? 1 : 2);
  si->elbase = 0;
  r[rA] = insn.Op2.reg;
  return true;
}

//----------------------------------------------------------------------
static jump_table_type_t is_jump_pattern1(switch_info_t *si, const insn_t &insn)
{
  jump_pattern1_t jp(si);
  if ( jp.match(insn) )
  {
    // jp.mark_switch_insns(3);
    si->flags |= SWI_HXNOLOWCASE;
    return si->get_shift() == 1 ? JT_ARM_LDRB : JT_ARM_LDRH;
  }
  return JT_NONE;
}

//----------------------------------------------------------------------
static jump_table_type_t is_jump_pattern2(switch_info_t *si, const insn_t &insn)
{
  jump_pattern2_t jp(si);
  if ( jp.match(insn) )
  {
    // jp.mark_switch_insns(3);
    si->flags |= SWI_HXNOLOWCASE;
    return JT_ARM_LDRH;
  }
  return JT_NONE;
}

//----------------------------------------------------------------------
static void create_align_before_table(ea_t table)
{
  if ( get_byte(table-1) == 0
    && is_unknown(get_flags(table-1))
    && get_byte(table-2) == 0
    && is_unknown(get_flags(table-2)) )
  {
    create_align(table-2, 2, 2);
  }
}

//----------------------------------------------------------------------
// TODO: handle align for byte table in ARM mode (align = 4 bytes)
static void create_align_after_table(ea_t end)
{
  if ( (end & 1) != 0           // odd address
    && get_byte(end) == 0 )
  {
    del_items(end, DELIT_SIMPLE);
    create_align(end, 1, 1);
  }
}

//----------------------------------------------------------------------
static void create_jump_table(switch_info_t *_si, const insn_t &, jump_table_type_t jtt)
{
  switch_info_t &si = *_si;
  ea_t table = si.jumps;
  create_align_before_table(table);
  if ( jtt == JT_ARM_LDRB )
    create_align_after_table(table+si.ncases);

  si.flags |= (si.defjump == BADADDR ? 0 : SWI_DEFAULT) | SWI_ELBASE | SWI_SEPARATE;
  // si.set_jtable_element_size(jtt == JT_ARM_LDRB ? 1 : 2);
  // si.elbase = insn.ea + (is_thumb_ea(insn.ea) ? 4 : 8);
}

//----------------------------------------------------------------------
static bool mips_check_for_table_jump(switch_info_t *si, const insn_t &insn)
{
  static is_pattern_t *const patterns[] =
  {
    is_jump_pattern1,
    is_jump_pattern2,
  };
  return check_for_table_jump(si, insn, patterns, qnumber(patterns), create_jump_table);
}

//----------------------------------------------------------------------
ssize_t idaapi mipsjt_is_switch(switch_info_t *si, const insn_t &insn)
{
    return ph.is_switch(si, insn);
}


static ssize_t idaapi PluginExtensionCallback(void * /*user_data*/, int event_id, va_list va)
{
	switch (event_id)
	{
    	case processor_t::ev_is_switch:
      {
        switch_info_t *si = va_arg(va, switch_info_t *);
        const insn_t *insn = va_arg(va, const insn_t *);
        return mipsjt_is_switch(si, *insn) ? 1 : 0;
      }
      default:
      break;
	}
	return 0;
}

int idaapi PluginStartup(void)
{
  // MIPSJT only works with MIPS code :)
  if ( ph.id != PLFM_MIPS )
    return PLUGIN_SKIP;

  msg("Loading MIPS Jump Table plugin %s\n", MIPSJT_VERSION);

 hook_to_notification_point(HT_IDP, PluginExtensionCallback, NULL);
  // if MIPS then this plugin is OK to use
  return PLUGIN_KEEP;
}


void idaapi PluginShutdown(void)
{
  msg("Shutting down MIPS Jump Table plugin\n");

  /* If not on MIPS, then don't overwrite is_switch */
  if (ph.id == PLFM_MIPS) {
		unhook_from_notification_point(HT_IDP, PluginExtensionCallback);
  }
}


bool idaapi PluginMain(size_t param)
{
}



/************************************************************
*
* Strings required for IDA Pro's PLUGIN descriptor block
*
************************************************************/

const char G_PLUGIN_COMMENT[] = "MIPS Jump Table fix";
const char G_PLUGIN_HELP[] = "This plugin adds Jump Table support to the MIPS process module"
  "of IDA, resolving switch/cases into properly analyzed code.";
const char G_PLUGIN_NAME[] = "MIPSJT: Jump table size";
const char G_PLUGIN_HOTKEY[] = "";


/**********************************************************************
*
*  This 'PLUGIN' data block is how IDA Pro interfaces with this plugin.
*
**********************************************************************/
plugin_t PLUGIN =
{
	// values
	IDP_INTERFACE_VERSION,
	0,				// plugin flags

	// functions
	PluginStartup,			// initialize
	PluginShutdown,			// terminate. this pointer may be NULL.
	PluginMain,			// invoke plugin

	// strings
	(char*)G_PLUGIN_COMMENT,	// long comment about the plugin
	(char*)G_PLUGIN_HELP,		// multiline help about the plugin
	(char*)G_PLUGIN_NAME,		// the preferred short name
	(char*)G_PLUGIN_HOTKEY		// the preferred hotkey
};

