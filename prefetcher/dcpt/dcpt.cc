#include <algorithm>
#include <bitset>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <boost/circular_buffer.hpp>
#include <boost/circular_buffer/base.hpp>
#include <list>
#include <map>
#include <math.h>
#include <stdexcept>
#include <vector>

#include "cache.h"


using std::string;
using std::invalid_argument;
using std::bitset;
using std::cout;
using std::cin;
using std::hex;
using std::dec;


//* Mask to get the first address in a block.
static const uint64_t blk_mask=~((static_cast<uint64_t>(1)<<LOG2_BLOCK_SIZE)-1);
/*****************************************************************************************************************************/
class idx_entry
{
  /**
  * @param tag used searching in the set.
  * @param last_addr it is the latest address asked by the instruction this entry is associated with.
  * @param last_prefetch it is the last address for which prefetching was requested.
  * @param delta_mask it has the largest number representable given n bits for representing a delta.
  * @param n number of bits per deltas entry.
  * @param deltas a circular buffer of deltas.
  * @param delta_bits number of bits per delta.
  * @param valid tells if this entry is valid in the set.
  */
    public:
    uint64_t tag,last_addr,last_prefetch;
    uint64_t delta_mask;
    uint n;
    boost::circular_buffer<std::int64_t> deltas;
    uint8_t delta_bits;
    bool valid;
    idx_entry(uint64_t tag=0,uint64_t addr=0,uint delta_bits=32,bool valid=false,uint n=19)
    {
        this->tag=tag;
        this->last_addr=addr;
        this->last_prefetch=0;
        this->valid=valid;
        this->delta_bits=delta_bits;
        this->delta_mask=(delta_bits<32)?(1<<delta_bits)-1:-1;
        this->deltas=boost::circular_buffer<std::int64_t>(n);
        this->n=n;
    }
    idx_entry(const idx_entry &x)
    {
      set(x);
    }
    void set(const idx_entry &x)
    {
      this->tag=x.tag;
      this->last_addr=x.last_addr;
      this->last_prefetch=x.last_prefetch;
      this->valid=x.valid;
      this->delta_bits=x.delta_bits;
      this->delta_mask=x.delta_mask;
      this->deltas=x.deltas;
      this->n=x.n;
    }
    /**
     * Add a new address into the deltas.
    */
    void insert(uint64_t addr)
    {
      std::int64_t delta=(std::int64_t)(addr-last_addr);
      /**
       * If It is an overflow set push 0 to circular buffer;
      */
      if(delta>delta_mask)
        deltas.push_back(0);
      /**
       * Ignore when addr == last_addr;
      */
      else if(delta!=0)
        deltas.push_back(delta);
      last_addr=addr;
    }

    /**
     * Algorithm requires use of latest few deltas, say i of them, in the circular buffer.
     * It searches for the occurance of the latest i deltas in the delta sequence before the last i deltas.
     * If found, the sequence after can be cadidates for prefetch.
     * @param i is the latest few deltas used for searching.
     * @param pf is an output variable for giving a list of prefetch candidates.
     * 
    */
    void get_prefetch_addresses(std::list<uint64_t> &pf,int i)
    {
      //* At least 2*i deltas should be there for the last i deltas to repeat.
      if(deltas.size()<2*i)
        return;
      /**
       * Search the deltas for the last i deltas in reverse direction.
      */
      auto dts=std::search(deltas.rbegin()+i,deltas.rend(),deltas.rbegin(),deltas.rbegin()+i);
      //* If delta sequence repetition found.
      if(dts!=deltas.rend())
      {
        uint64_t pf_addr=last_addr;
        //* Generate the addresses and have only one address representing each cache block.
        for(auto it=deltas.rbegin()+i;it!=dts;++it)
        {
          pf_addr+=*it;
          if(pf_addr==last_prefetch)
          {
            pf.clear();
          }
          else
          {
            //* Find if another prefetch candidate belongs to the same cache block.
            auto same_blk=[pf_addr](uint64_t ad){
              return (pf_addr&blk_mask)==(ad&blk_mask);};
            auto dup=std::find_if(pf.begin(),pf.end(),same_blk);
            if(dup==pf.end())
            {
              pf.push_back(pf_addr);
            }
          }
        }
      }
    }
    bool operator==(const idx_entry &b1)
    {
        return this->tag==b1.tag;
    }
    friend std::ostream& operator<<(std::ostream& os, const idx_entry &p)
    {
      os<<"("<<hex<<p.tag<<dec<<","<<p.last_addr<<" , "<<p.last_prefetch<<","<<p.valid<<")";
      return os;
    }
};


//* Abstract Base class for index table sets.
class idx_set
{
    protected:
    /**
    * @param ways is the number of lines in the set.
    */
    const uint ways;

    public:
    
    idx_set(const uint ways) :ways(ways)
    {}

    //* Method for simulating memory access in a cache set.
    virtual void insert(const idx_entry &ent,std::list<idx_entry>::iterator &it)=0;
    virtual std::list<idx_entry>::iterator find(uint64_t tag)=0;
    virtual void access(std::list<idx_entry>::iterator it)=0;
};


/*****************************************************************************************************************************/
class lru_idx_set : public idx_set
{
    /**
    * * A queue of all the valid lines in the set, so no need for valid bit in idx_entry.
    */
    std::list<idx_entry> idx_entries;
    const uint delta_bits;
    public:
    static const string replacement_algo;
    
    lru_idx_set(uint ways,uint delta_bits) : idx_set(ways),delta_bits(delta_bits)
    {}

    /**
    * * Implements memory access with LRU replacement algorithm.
    * * Returns if it was a hit or not.
    * TODO: Sperate out reads and writes
    * TODO: Count the number of modified lines replaced.
    */

    virtual std::list<idx_entry>::iterator find(uint64_t tag) override
    {
      for(auto it=idx_entries.begin();it!=idx_entries.end();++it)
        if(it->tag==tag)
          return it;
      return idx_entries.end();
    }

    //* Puts the element at the end of the list. The farther the element from the head the more recent it has been accessed.
    virtual void access(std::list<idx_entry>::iterator it) override
    {
        idx_entries.splice(idx_entries.end(),idx_entries,it);
    }
    virtual bool is_end(std::list<idx_entry>::iterator &it)
    {
      return it==idx_entries.end();
    }
    //* Assumes the entry ent is not in this set. Use find before the function to check.
    virtual void insert(const idx_entry &ent,std::list<idx_entry>::iterator &it) override
    {
      //* Re-use the node that is being replaced.
      if(idx_entries.size()==ways)
      {
          idx_entries.splice(idx_entries.end(),idx_entries,idx_entries.begin());
          std::prev(idx_entries.end())->set(ent);
      }
      //* No need for replacement, just push the line to the queue.
      else
      {
          idx_entries.push_back(ent);
      }
    }
    //* Prints the tag of lines in the set.
    void print()
    {
        cout<<"lines : ";
        for(const auto &i:idx_entries)
            cout<<i<<" || ";
        cout<<"\n";
    }
};
const string lru_idx_set::replacement_algo = "LRU";

/*****************************************************************************************************************************/
template<class idx_set>
class IndexTable
{
    /**
    * @param ways is the set associativity of the cache.
    * @param no_of_sets is the number of sets in the cache.
    * @param set_bits no. of bits required for indexing sets.
    * @param tag_bits no. of bits required for tag.
    * @param set_mask for getting only the index portion of the address.
    * @param tag_mask for getting only the tag portion of the address.
    * @param addr_bits address length.
    * @param *c points to the cache this table is associated with.
    * @param no_of_deltas_to_search The no. of latest few deltas to seach in the circular buffer of deltas.
    */
    protected:
    const string name,replacement_algo;
    const uint ways,no_of_sets,blk_size;
    const uint n,delta_bits;
    const uint no_of_deltas_to_search;
    CACHE *c;
    uint byte_bits,set_bits,tag_bits;
    std::vector<idx_set> sets;
    uint64_t byte_mask,set_mask,tag_mask;
    const uint addr_bits=64;
    public:
    IndexTable(const string &name,const string &replacement_algo,const uint no_of_sets,const uint ways,const uint blk_size,const uint n,const uint delta_bits,const uint no_of_deltas_to_search,CACHE *c) : 
    name(name),replacement_algo(replacement_algo),ways(ways),no_of_sets(no_of_sets),blk_size(blk_size),n(n),delta_bits(delta_bits),no_of_deltas_to_search(no_of_deltas_to_search)
    {
        if(no_of_sets==0)
            throw invalid_argument("no_of_sets should be a positive integer");
        if(ways==0)
            throw invalid_argument("Ways should be a positive integer");
        byte_bits= log2(blk_size);
        set_bits = log2(no_of_sets);
        tag_bits = addr_bits-set_bits-byte_bits;
        if(byte_bits<addr_bits)
            byte_mask=((1<<byte_bits)-1);
        else
         byte_mask=-1;
        if(set_bits<addr_bits)
            set_mask=((1<<set_bits)-1)<<byte_bits;
        else
            set_mask=-1;
        if(tag_bits<addr_bits)
            tag_mask=((1<<tag_bits)-1)<<(byte_bits+set_bits);
        else
            tag_mask=-1;
        for(uint i=0;i<no_of_sets;++i)
        {
            idx_set N(ways,delta_bits);
            sets.push_back(N);
        }
        this->c=c;
    }
    
    //* Overloading << operator for output.
    friend std::ostream& operator<<(std::ostream& os, const IndexTable &p)
    {
        return os
            <<"\nCache Name             = "<<p.name
            <<"\nReplacement Algorithm  = "<<p.replacement_algo
            <<"\nWays                   = "<<p.ways
            <<"\nNo of sets             = "<<p.no_of_sets
            <<"\nbyte_bits              = "<<p.byte_bits
            <<"\nset_bits               = "<<p.set_bits
            <<"\ntag_bits               = "<<p.tag_bits
            <<"\nbyte_mask              = "<<bitset<8*sizeof(uint64_t)>(p. byte_mask)
            <<"\nset_mask               = "<<bitset<8*sizeof(uint64_t)>(p.set_mask)
            <<"\ntag_mask               = "<<bitset<8*sizeof(uint64_t)>(p.tag_mask);
    }
    uint64_t get_blk_addr(uint64_t addr)
    {
        return addr&(tag_mask+set_mask);
    }

    //* Checks if the block containing ad is in cache.
    bool in_cache(uint64_t ad)
    {
        auto set_no = c->get_set(ad);
        auto way = c->get_way(ad,set_no);
        auto idx=set_no * c->NUM_WAY + way;
        if(way<c->NUM_WAY)
          return c->block[idx].valid and (c->block[idx].v_address&blk_mask)==(ad&blk_mask);
        else 
          return false;
    }

    //* Used to check of the address's cache block is in any of the queues.
    template<class Iterator>
    bool is_in(const Iterator &begin,const Iterator &end,uint64_t ad)
    {
      static_assert(
        std::is_same<typename std::iterator_traits<Iterator>::value_type,PACKET>(), 
      "The value_type must be PACKET.");
      for(auto it=begin;it!=end;++it)
      {
        if((it->address&blk_mask)!=0 and (it->v_address&blk_mask)==(ad&blk_mask))
          return true;
      }
      return false;
    }
    bool in_queues_or_cache(uint64_t ad)
    {
      return is_in(c->RQ.begin(),c->RQ.end(),ad)      // Read Queue
          or is_in(c->WQ.begin(),c->WQ.end(),ad)      // Write Queue
          or is_in(c->PQ.begin(),c->PQ.end(),ad)      // Prefetch Queue
          or is_in(c->MSHR.begin(),c->MSHR.end(),ad)  // MSHR's
          or in_cache(ad);
    }
    //* Remove addresses that are already in Cache or is in-flight.
    void prefetch_filter(std::list<uint64_t> &candidates)
    {
      auto in_Q_or_cache=[this](uint64_t ad) {return this->in_queues_or_cache(ad);};
      std::remove_if(candidates.begin(),candidates.end(),in_Q_or_cache);

    }
    //* Trains DCPT given the missed load or store address and it's PC.
    std::list<uint64_t> dcpt(uint64_t pc,uint64_t addr)
    {
      uint64_t set_no= (set_mask&pc)>>byte_bits;
      std::list<uint64_t> candidates;
      //cout<<"\nSet no : "<<set_no<<"  Blk_addr : "<<blk_addr;
      uint64_t tag   = pc;
      auto it=sets[set_no].find(tag);
      //* If the PC value is new create a new entry.
      if(sets[set_no].is_end(it))
      {
        idx_entry ent(tag,addr,delta_bits,true,n);
        sets[set_no].insert(ent,it);
      }
      //* If not then update the entry if the miss address is not the same as before.
      else if(addr!=it->last_addr)
      {
        it->insert(addr);
        sets[set_no].access(it);
        //* Search for the last
        it->get_prefetch_addresses(candidates,no_of_deltas_to_search);
        prefetch_filter(candidates);
        if(not candidates.empty())
          it->last_prefetch=*std::prev(candidates.end());
      }
      return candidates;
    }

};
/*****************************************************************************************************************************/
//* Maps a cache to it's DCPT.
std::map<CACHE*,IndexTable<lru_idx_set>*> dcpts;
/*****************************************************************************************************************************/

//* Creates a DCPT for itself.
void CACHE::prefetcher_initialize()
{
  std::cout << NAME << " Delta Correlating Prefetcher\n";
  dcpts[this]= new IndexTable<lru_idx_set>("DCPT","LRU",128,4,BLOCK_SIZE,19,12,2,this);
}

void CACHE::prefetcher_cycle_operate(){}

uint32_t CACHE::prefetcher_cache_operate(uint64_t addr, uint64_t ip, uint8_t cache_hit, uint8_t type, uint32_t metadata_in)
{
  //* DCPT is trained on demand access misses.
  if(cache_hit==0 and type!=PREFETCH)
  {
    
    auto prefetchable=dcpts[this]->dcpt(ip,addr);
    for(const auto &p:prefetchable)
    {
      prefetch_line(p,true,0);
    }
  }
  return metadata_in;
}

uint32_t CACHE::prefetcher_cache_fill(uint64_t addr, uint32_t set, uint32_t way, uint8_t prefetch, uint64_t evicted_addr, uint32_t metadata_in)
{
  return metadata_in;
}

//* Destroy the DCPT
void CACHE::prefetcher_final_stats() {
  delete dcpts[this];
  dcpts.erase(this);
}
