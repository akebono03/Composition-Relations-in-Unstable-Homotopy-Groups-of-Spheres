from re import template
from weakref import ReferenceType
from flask import Flask, render_template, request #追加
from jinja2 import Template
import sqlite3
import numpy as np
import pandas as pd
import sympy as sp
import os

app=Flask(__name__)

df=pd.read_csv('./HyoujiGen.csv')
display_list=df['display'].unique().tolist()
stable_display_list=df[(df['kinds']==0)]['display'].unique().tolist()
symbol_list=[' ',',','{','}','[',']','+']
stable_symbol_list=[' ',',','(',')','〈','〉','+']

n=2
k=0
tt=0
coe_list=[1]*6
coe_list0=[1]*6
displays=['','','','','','']
stable_displays=['','','','','','']
relation_tex_list=[]
reference_tex_list=[]
relation_count=0
display_mode=''
symbols0=['','','','','','','']
stable_symbols0=['','','','','','','']

@app.route('/')
def relation():
  return render_template('relation.html',display_list=display_list,coe_list0=coe_list0\
,n=n,k=k,tt=tt,coe_list=coe_list,displays=displays,display_mode=display_mode\
,relation_tex_list=relation_tex_list,reference_tex_list=reference_tex_list\
,relation_count=relation_count,symbol_list=symbol_list,symbols0=symbols0\
,stable_display_list=stable_display_list,stable_symbol_list=stable_symbol_list\
,stable_displays=stable_displays,stable_symbols0=stable_symbols0)#変更

@app.route('/register', methods=['post'])
def register():
  n=request.form['n']
  n=int(n)

  tt=request.form['tt']
  tt=int(tt)

  db_name='sphere.db'
  conn=sqlite3.connect(db_name)
  # df=pd.read_csv('./sphere.csv')
  # df.to_sql('sphere', conn, if_exists='replace')
  # df=pd.read_csv('./HyoujiGen.csv')
  # df.to_sql('gen', conn, if_exists='replace')
  # df=pd.read_csv('./TBtable.csv')
  # df.to_sql('TBtable', conn, if_exists='replace')
  # df=pd.read_csv('./sphere_relation2.csv')
  # df.to_sql('sphere_relation', conn, if_exists='replace')
  c=conn.cursor()

  inf=float('inf')

#dict_factoryの定義
  def dict_factory(cursor,row):
    d={}
    for idx,col in enumerate(cursor.description):
      d[col[0]]=row[idx]
    return d

#row_factoryの変更(dict_factoryに変更)
  c.row_factory=dict_factory

  def Dot(A,B):
    return sp.expand( (A.transpose()*B)[0,0])

  def cyclic_order(r,m):
    res=0
    for res in range(1,m+1):
      if r*res%m==0:break
    return res

  def el_id(disp):
    gen_query=f'select*from gen where display="{disp}"'
    for row in c.execute(gen_query):
      res=row['id']
    return res

  def k_dim(el_list):
    res=0
    for elem in el_list:
      gen_query=f'select*from gen where id="{elem}"'
      for row in c.execute(gen_query):
        res+=row['k']
    return res

  class HomotopyGroup:
    def __init__(self,n,k):
      self.n=int(n)
      self.k=int(k)

      if k<=-1:
        query=f'select*from sphere where n={0} and k={-1}'
        query_count=f'select count( * ) from sphere where n={0} and k={-1}'
      elif k+2>=n:
        query=f'select*from sphere where n={n} and k={k}'
        query_count=f'select count( * ) from sphere where n={n} and k={k}'
      else:
        query=f'select*from sphere where n={k+2} and k={k}'
        query_count=f'select count( * ) from sphere where n={k+2} and k={k}'
      self.query = query
      self.query_count= query_count

    def direct_sum(self):
#直和成分の個数を与えるメソッド
      for row in c.execute( self.query_count):
        res=row['count( * )']
      return res

    def order_list(self):
#orderのリストを与えるメソッド
      try:res=[row['orders'] if row['orders']==inf else int(row['orders']) for row in c.execute(self.query)]
      except:res=[0]
      return res

    def group_order(self):
      res=max(self.order_list())
      return res

    def max_direct_sum(self):
      nn=[self.n*2-1,self.n-1, self.n,self.n*2-1,self.n-1]
      kk=[self.k-self.n+2, self.k,self.k,self.k-self.n+1, self.k-1]
      m_d_sum=[HomotopyGroup( nn[i],kk[i]).direct_sum() for i in range(5)]
      return max(m_d_sum)

    def query_id(self,id):
      if self.k<=-1:res=f'select*from sphere where n={0} and k={-1} and id={id}'
      elif self.k+2>=self.n:res=f'select*from sphere where n={self.n} and k={self.k} and id={id}'
      else:res=f'select*from sphere where n={self.k+2} and k={self.k} and id={id}'
      return res

    def rep_list(self,id):
#表示元を合成で表示する際の数字のリストを与えるメソッド
      c.execute( self.query_id(id))
      res=list(map(int, c.fetchone()['Element'].split()))
      return res

    def gen_coe_list(self,id):
#生成元の表示元による一次結合の係数のリストを与えるメソッド
      for row in c.execute(self.query_id(id)):
        res=list(map(int, row['gen_coe'].split()))
      del res[self.direct_sum():]
#リストの長さをdirect_sumの数にする
      return res

    def el_dim_list(self, el_list):
#表示元の境目の次元のリストを与えるメソッド
      res=[self.n]
      for i,elem in enumerate(el_list):
        gen_query=f'select*from gen where id="{elem}"'
        for row in c.execute( gen_query):
          res.append( res[i]+row['k'])
      return res

    def pi_tex(self):
      res=f'\pi_{ {self.n+self.k} }^{ {self.n} }'
      return res

    def group_structure(self):
      group=[]
      for row in c.execute(self.query):
        if row['orders']==0:group.append('0')
        elif row['orders']==inf:group.append('Z')
        else:
          try:group.append(f"Z_{ {int(row['orders'])} }")
          except:group.append('0')
      self_direct_sum= self.direct_sum()
      group_gen= [self.rep_linear_tex( self.gen_coe_list(j)) for j in range(self_direct_sum)]
      group_tex_list= [gr+'\{'+gen+'\}' for (gr,gen) in zip(group,group_gen)]
      return ' \oplus '.join( group_tex_list)

    def stable_group_structure( self):
      group=[]
      for row in c.execute(self.query):
        if row['orders']==0:group.append('0')
        elif row['orders']==inf:group.append('Z')
        else:
          try:group.append(f"Z_{ {int(row['orders'])} }")
          except:group.append('0')
      self_direct_sum= self.direct_sum()
      gen_id_list_list= [self.rep_list(j) for j in range(self_direct_sum)]
      group_gen=[]
      for gen_id_list in gen_id_list_list:
        gen_latex=''
        for gen_id in gen_id_list:
          gen_query= f'select*from gen where id="{gen_id}"'
          for row in c.execute(gen_query):
            if '{3,' in row['latex'] or '{4,' in row['latex']:gen_latex= gen_latex+' '+row['latex']+'*}'
            elif row['id']==174:gen_latex= gen_latex+' '+row['latex'] +'_{*}'
            else:gen_latex= gen_latex+' '+row['latex']
        group_gen.append( gen_latex)
      group_tex_list= [gr+'\{'+gen+'\}' for (gr,gen) in zip(group,group_gen)]
      return ' \oplus '.join( group_tex_list)

    def el_sus_list(self,el_list):
      res=[]
      for i,elem in enumerate(el_list):
        gen_query=f'select* from gen where id="{elem}"'
        for row in c.execute( gen_query):
          res.append( self.el_dim_list(el_list)[i] -row['n'])
      res.append( self.el_dim_list(el_list)[-1])
      return res

    def delete_iota(self, el_list,el_coe_list):
      delete_num=[]
      for i,elem in enumerate(el_list):
        if elem==1 and el_coe_list[i]==1 and (i>=1 or (i==0 and len(el_list)>=2)): delete_num.append(i)
      res_el_list=[el_list[i] for i in range(len(el_list)) if i not in delete_num]
      res_el_coe_list= [el_coe_list[i] for i in range(len(el_list)) if i not in delete_num]
      return res_el_list, res_el_coe_list

    def can_take_out_el_coe( self,el_list,i):
      sus_list= self.el_sus_list(el_list)
      dim_list= self.el_dim_list(el_list)
      res=False
      if dim_list[i+1] in {1,3,7}:res=True
      elif sus_list[i+1:]!=[]:
        if min(sus_list[i+1:]) >=1:res=True
      elif len(el_list)==i+1:res=True
      return res

    def el_coe_out(self, el_list,el_coe_list):
      out_coe=1
      for i in range(len(el_list)):
        if self.can_take_out_el_coe(el_list,i):
          out_coe= out_coe*el_coe_list[i]
          el_coe_list[i]=1
      res_el_list, res_el_coe_list= self.delete_iota(el_list, el_coe_list)
      return res_el_list, res_el_coe_list,out_coe

    def sub_comp(self,el_list, el_coe_list,i,j):
      res_el=el_list[i:i+j]
      res_coe=el_coe_list[i:i+j]
      return res_el,res_coe

    def sub_comp_list(self, elli,el_coeli,t):
      el_li=elli
      el_coe_li=el_coeli
      el_dim_li= self.el_dim_list(el_li)
      res_n,res_k=[],[]
      res_el,res_coe=[],[]
      bin_t=bin(t)[2:]
      bin_t0='0'*(len(el_li) -1-len(bin_t))+bin_t+'1'
      j=1
      for i in range(len(el_li)):
        if i==0:res_n.append( el_dim_li[0])
        elif bin_t0[i-1]=='1':res_n.append( el_dim_li[i])
        if bin_t0[i]=='1':
          sub_comp= self.sub_comp(el_li, el_coe_li,i-j+1,j)
          res_el.append( sub_comp[0])
          res_coe.append( sub_comp[1])
          j=1
        else:j+=1
      for i in range(len(res_n)):
        if i<= len(res_n)-2:res_k.append( res_n[i+1]-res_n[i])
        else:res_k.append( el_dim_li[-1]-res_n[-1])
      return res_n,res_k, res_el,res_coe

    def el_tex(self,el_li):
#表示元のtex表示を与えるメソッド
      el_dim_li= self.el_dim_list(el_li)
      res=''
      sq_cnt=1
      for i,elem in enumerate(el_li):
        gen_query=f'select*from gen where id="{elem}"'
        for row in c.execute(gen_query):
          if row['kinds']==0:
            if el_dim_li[i]< row['n']:res+='{'+row['latex'] +f'_{ {el_dim_li[i]} }'+'(Not Defined)}'
            elif i==0 or el_li[i-1]!=el_li[i]:sq_cnt=1
#一番最初か、前のidと違うとき、カウントを１にする。
            else:sq_cnt+=1
#前のidと同じときにカウントを＋１
            if i== len(el_li)-1:
#最後のときにtexを追加
              if el_dim_li[i] >=row['n']:
                if '{3,' in row['latex'] or '{4,' in row['latex']:res+='{' +row['latex'] +f'{el_dim_li[i-sq_cnt+1]}' +'} }'
                else:res+='{' +row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                if sq_cnt>=2:res= res[:-1]+f'^{ {sq_cnt} }'+'}'
            elif el_li[i]!= el_li[i+1]:
#次のidと違うときにtexを追加
              if el_dim_li[i] >=row['n']:
                if '{3,' in row['latex'] or '{4,' in row['latex']:res+='{' +row['latex'] +f'{el_dim_li[i-sq_cnt+1]}'+'} }'
                else:res+='{'+ row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                if sq_cnt>=2: res= res[:-1]+f'^{ {sq_cnt} }'+'}'
#カウントの数をべきにする。
#次のidと同じ場合は何もしない
          elif el_dim_li[i] <row['n']:res+='{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'(Not Defined)}'
          elif el_dim_li[i] ==row['n']:res+='{' +row['latex']+'}'
          elif el_dim_li[i]== row['n']+1:res+='{'+' E '+row['latex']+'}'
          else:res+='{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'}'
      if 0 in el_li:res='0'
      return res

    def el_coe_tex(self,elli,el_coeli=[1]*6):
      el_li,el_coe_li=self.delete_iota(elli,el_coeli)
      el_dim_li=self.el_dim_list(el_li)
      len_el_li=len(el_li)
      res=''
      sq_cnt=1
      for i,elem in enumerate(el_li):
        gen_query=f'select*from gen where id="{elem}"'
        for row in c.execute(gen_query):
          if row['kinds']==0:
            if el_dim_li[i]<row['n']:
              if el_coe_li[i]==1:res+='{'+row['latex']+f'_{ {el_dim_li[i]} }'+'(Not Defineda)}'
              elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+row['latex']+f'_{ {el_dim_li[i]} }'+'(Not Defineda)}'
              else:res+='('+f'{el_coe_li[i]}'+'{'+row['latex']+f'_{ {el_dim_li[i]} }'+'(Not Defineda)})'
            elif i==0 or el_li[i-1]!=el_li[i] or (el_li[i-1]==el_li[i] and el_coe_li[i]!=1):sq_cnt=1
#一番最初か、前のidと違うとき、カウントを１にする。
            else:sq_cnt+=1;el_coe_li[i]=el_coe_li[i-1]
#前のidと同じときにカウントを＋1
            if i==len_el_li-1:
#最後のときにtexを追加
              # if el_dim_li[i]>=row['n']:
              if el_dim_li[i]<row['n']:continue
              if '{3,' in row['latex'] or '{4,' in row['latex']:
                if el_coe_li[i]==1:res+='{'+row['latex']+f'{el_dim_li[i-sq_cnt+1]}'+'} }'
                elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+row['latex']+f'{el_dim_li[i-sq_cnt+1]}'+'} }'
                else:res+='('+f'{el_coe_li[i]}'+'{'+row['latex']+f'{el_dim_li[i-sq_cnt+1]}'+'} })'
              else:
                if el_coe_li[i]==1:res+='{'+row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                else:res+='('+f'{el_coe_li[i]}'+'{'+row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'})'
              if sq_cnt<2:continue
              if res[-1]==')':res=res[:-2]+f'^{ {sq_cnt} }'+'})'
              else:res=res[:-1]+f'^{ {sq_cnt} }'+'}'
            elif el_li[i]!=el_li[i+1] or (el_li[i]==el_li[i+1] and el_coe_li[i+1]!=1):
#次のidと違うときにtexを追加
              if el_dim_li[i]<row['n']:continue
              if '{3,' in row['latex'] or '{4,' in row['latex']:
                if el_coe_li[i]==1:res+='{'+row['latex']+f'{el_dim_li[i-sq_cnt+1]}'+'} }'
                elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+row['latex']+f'{el_dim_li[i-sq_cnt+1]}'+'} }'
                else:res+='('+f'{el_coe_li[i]}'+'{'+row['latex']+f'{el_dim_li[i-sq_cnt+1]}'+'} })'
              else:
                if el_coe_li[i]==1:res+='{'+row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                else:res+='('+f'{el_coe_li[i]}'+'{'+row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'})'
              if sq_cnt<2:continue
# カウントの数をべきにする。
              if res[-1]==')':res=res[:-2]+f'^{ {sq_cnt} }'+'})'
              else:res=res[:-1]+f'^{ {sq_cnt} }'+'}'
#次のidと同じ場合は何もしない
          elif el_dim_li[i]<row['n']:
            if el_coe_li[i]==1:res+='{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'(Not Defined)}'
            elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'(Not Defined)}'
            else:res+='('+f'{el_coe_li[i]}'+'{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'(Not Defined)})'
          elif el_dim_li[i]==row['n']:
            if el_coe_li[i]==1:res+='{'+row['latex']+'}'
            elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+row['latex']+'}'
            else:res+='('+f'{el_coe_li[i]}'+'{'+row['latex']+'})'
          elif el_dim_li[i]==row['n']+1:
            if el_coe_li[i]==1:res+='{'+' E '+row['latex']+'}'
            elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+' E '+row['latex']+'}'
            else:res+='('+f'{el_coe_li[i]}'+'{'+' E '+row['latex']+'})'
          else:
            if el_coe_li[i]==1:res+='{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'}'
            elif len_el_li==1:res+=f'{el_coe_li[i]}'+'{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'}'
            else:res+='('+f'{el_coe_li[i]}'+'{'+' E '+f"^{ {el_dim_li[i]-row['n']} }"+row['latex']+'})'
      return res

    def rep_linear_tex(self,coe,totalcoe=1):
      rep_coe=[c*totalcoe for c in coe]
      ord_li=self.order_list()
      direct_sum=self.direct_sum()
      if ord_li==[0]:res='0'
      elif rep_coe!=[]:
        symbol_li=['x00','x01','x02','x03','x04','x05','x06','x07','x08','x09','x10','x11']
        X=sp.Matrix([sp.Symbol(symbol_li[i]) for i in range(direct_sum)])
        def mod_coe(i):
          try:
            if ord_li[i]==inf: return rep_coe[i]
            elif rep_coe[i]%ord_li[i]>ord_li[i]//2: return rep_coe[i]%ord_li[i]-ord_li[i]
            else: return rep_coe[i]%ord_li[i]
          except: return rep_coe[i]
        A=sp.Matrix([mod_coe(i) for i in range(direct_sum)])
        res=str(Dot(X,A)).replace('*x','x')
        for i in range(direct_sum):
          res=res.replace(symbol_li[i],self.el_tex(self.rep_list(i)))
      else:res=''
      return res

    def P_coe(self,id):
      res=[]
      ref_tex=''
      order_list=self.order_list()
      try:
        if order_list==[0] or order_list==[]:res=[0]*12
        else:
          queryid=f'select*from sphere where n={self.n} and k={self.k} and id={id}'
          for row in c.execute(queryid):
            if row['P_coe'] is None:continue
            res=list(map(int,row['P_coe'].split()))
            ref_tex=row['P']
      except:pass
      del res[HomotopyGroup((self.n-1)//2,(self.n+2*self.k-3)//2).direct_sum():]
#リストの長さをdirect_sumの個数にする
      return res,ref_tex

    def E_coe(self,id):
      res=[]
      ref_tex=[]
      for row in c.execute(self.query_id(id)):
        if row['E_coe'] is None:continue
        res=list(map(int,row['E_coe'].split()))
        ref_tex=row['E']
      hg=HomotopyGroup(self.n+1,self.k) if self.k+2>=self.n else HomotopyGroup(self.k+2,self.k)
      del res[hg.direct_sum():]
      return res,ref_tex

    def H_coe(self,id):
      res=[]
      ref_tex=''
      if self.k+2>=self.n:
        for row in c.execute(self.query_id(id)):
          if row['H_coe'] is None:continue
          res=list(map(int,row['H_coe'].split()))
          ref_tex=row['H']
      else:res=[0]*12
      del res[HomotopyGroup(2*self.n-1,self.k-self.n+1).direct_sum():] 
#リストの長さをdirect_sumの個数にする
      return res,ref_tex

    def P_image_tex(self,id):
      if self.n%2==1:
        P_hg=HomotopyGroup((self.n-1)//2,(self.n+2*self.k-3)//2)
        self_P_coe=self.P_coe(id)
        res=P_hg.rep_linear_tex(self_P_coe[0])
        res_ref=self_P_coe[1]
      else:res,res_ref='',''
      return res,res_ref

    def E_image_tex(self,id):
      E_hg=HomotopyGroup(self.n+1,self.k)
      self_E_coe=self.E_coe(id)
      res=E_hg.rep_linear_tex(self_E_coe[0])
      res_ref=self_E_coe[1]
      return res,res_ref

    def H_image_tex(self,id):
      H_hg=HomotopyGroup(2*self.n-1,self.k-self.n+1)
      self_H_coe=self.H_coe(id)
      res=H_hg.rep_linear_tex(self_H_coe[0])
      res_ref=self_H_coe[1]
      return res,res_ref

    def rep_coe_to_id_list(self,repcoeli):
      res_id=[i for i in range(self.direct_sum()) if repcoeli[i]!=0]
      res_coe=[repcoeli[i] for i in res_id]
      return res_id,res_coe

    def rep_coe_to_el_list(self,repcoeli):
      id_li=self.rep_coe_to_id_list(repcoeli)
      res_el=[self.rep_list(i) for i in id_li[0]]
      res_coe=id_li[1]
      return res_el,res_coe

    def P_coe_matrix(self):
      matrix_li=[]
      d_sum=self.direct_sum()
      for id in range(d_sum):
        for row in c.execute(self.query_id(id)):
          int_li=list(map(int,row['P_coe'].split()))
        del int_li[d_sum:]
        matrix_li.append(int_li)
      return sp.Matrix(matrix_li)

    def E_coe_matrix(self):
      matrix_li=[]
      d_sum=self.direct_sum()
      for id in range(d_sum):
        for row in c.execute(self.query_id(id)):
          int_li=list(map(int,row['E_coe'].split()))
        del int_li[d_sum:]
        matrix_li.append(int_li)
      return sp.Matrix(matrix_li)

    def H_coe_matrix(self):
      matrix_li=[]
      d_sum=self.direct_sum()
      for id in range(d_sum):
        for row in c.execute(self.query_id(id)):
          int_li=list(map(int,row['H_coe'].split()))
        del int_li[d_sum:]
        matrix_li.append(int_li)
      return sp.Matrix(matrix_li)

    def rep_to_gen_matrix(self):
      matrix_li=[]
      d_sum=self.direct_sum()
      for id in range(d_sum):
        for row in c.execute(self.query_id(id)):
          int_li=list(map(int,row['gen_coe'].split()))
        del int_li[d_sum:]
        matrix_li.append(int_li)
      return sp.Matrix(matrix_li)

    def rep_coe_to_gen_coe(self,repcoeli):
      repcoematrix=sp.Matrix([repcoeli])
      return (repcoematrix*self.rep_to_gen_matrix().inv()).tolist()[0]

    def gen_coe_to_rep_coe(self,gencoeli):
      gencoematrix=sp.Matrix([gencoeli])
      return (gencoematrix*self.rep_to_gen_matrix()).tolist()[0]

    def mod_gen_coe_list(self,gencoe):
      order_li=self.order_list()
      d_sum=self.direct_sum()
      def mod_coe(i):
        oi,gi=order_li[i],gencoe[i]
        if oi==inf:return gi
        elif gi%oi>oi//2:return gi%oi-oi
        else:return gi%oi
      return [mod_coe(i) for i in range(d_sum)]

    def group_is_zero(self):
      res=False
      for row in c.execute(self.query):
        res=True if row['orders']==0 else False
      return res

    def sub_comp_tex_list(self,el_li,el_coe_li,t):
      sub_comp_li=self.sub_comp_list(el_li,el_coe_li,t)
      res=[]
      for i in range(len(sub_comp_li[0])):
        sub_n=sub_comp_li[0][i]
        sub_k=sub_comp_li[1][i]
        sub_el_li=sub_comp_li[2][i]
        sub_el_coe_li=sub_comp_li[3][i]
        sub_hg=HomotopyGroup(sub_n,sub_k)
        res.append(sub_hg.el_coe_tex(sub_el_li,sub_el_coe_li))
      return res


  class ElementLinear:
    def __init__(self,n,k,coe_list):
      self.n=n
      self.k=k
      self.coe_list=coe_list

    def direct_sum(self):
      hg=HomotopyGroup(self.n,self.k)
      return hg.direct_sum()

    def coe_cut(self):
      return self.coe_list[:self.direct_sum()]

    def E_coe(self):
      M=np.array([self.coe_cut()])
      hg=HomotopyGroup(self.n,self.k)
      d_sum=hg.direct_sum()
      N=np.array([hg.E_coe(i)[0] for i in range(d_sum)])
      try:      
        if type((M@N)[0])==list:res=(M@N)[0]
        else:res=(M@N)[0].tolist()
        ref_li=[hg.E_coe(i)[1] for i in range(d_sum) if self.coe_list[i]!=0 and hg.E_coe(i)[1] is not None]
      except ValueError:res,ref_li=[],[]
      if res==0:res=[0]
      return res,ref_li

    def rep_linear_order(self):
      d_sum=self.direct_sum()
      res=0
      hg=HomotopyGroup(self.n,self.k)
      order_li=hg.order_list()
      if inf in order_li:res=inf
      else:res=max([cyclic_order(self.coe_list[i],int(order_li[i])) for i in range(d_sum)])
      return res

    def linear_to_el_list(self):
      res_el,res_coe=[],[]
      if np.count_nonzero(self.coe_list)==1:
        for j in range(len(self.coe_list)):
          if self.coe_list[j]==0:continue
          hg=HomotopyGroup(self.n,self.k)
          res_el=hg.rep_list(j)
          res_coe=[1 if i!=len(res_el)-1 else self.coe_list[j] for i in range(len(res_el))]
      return res_el,res_coe


  class Element:
    def __init__(self,n,ellist=[1],el_coelist=[1]*6,total_coe=1):
      self.n=n
      self.ellist=ellist
      self.el_coelist=el_coelist
      self.total_coe=total_coe
      self.k = k_dim(ellist)

    def tex(self):
      hg=HomotopyGroup(self.n,self.k)
      el_coe_tex=hg.el_coe_tex(self.ellist,self.el_coelist)
      if self.total_coe==1:res = el_coe_tex
      elif len(self.ellist)==1 and self.el_coelist[0]==1:res=str(self.total_coe)+el_coe_tex
      else:res=str(self.total_coe)+'('+el_coe_tex+')'
      return res

    def dim_list(self):
      hg=HomotopyGroup(self.n,self.k)
      return hg.el_dim_list(self.ellist)

    def sus_list(self):
      dim_list=self.dim_list()
      res=[]
      for i,elem in enumerate(self.ellist):
        gen_query=f'select*from gen where id="{elem}"'
        for row in c.execute(gen_query):
          res.append(dim_list[i]-row['n'])
      return res

    def desus_max(self):
      sus_list=self.sus_list()
      if sus_list!=[]:res=min(sus_list)
      else:res=0
      return res

    def delete_iota(self):
      del_num=[]
      for i, elem in enumerate(self.ellist):
        if elem==1 and self.el_coelist[i]==1 and (i>=1 or (i==0 and len(self.ellist)>=2)):del_num.append(i)
      res_el=[self.ellist[i] for i in range(len(self.ellist)) if i not in del_num]
      try:res_coe=[self.el_coelist[i] for i in range(len(self.ellist)) if i not in del_num] 
      except IndexError:res_coe=[]    
      return res_el,res_coe

    def can_take_out_el_coe(self,i):
      sus_list=self.sus_list()
      dim_list=self.dim_list()
      res=False
      if dim_list[i+1] in {1,3,7}:res=True
      if sus_list[i+1:]!=[]:
        if min(sus_list[i+1:])>=1:res=True
      elif len(self.ellist)==i+1:res=True
      return res

    def el_coe_out(self):
      out_coe=self.total_coe
      for i in range(len(self.ellist)):
        if self.can_take_out_el_coe(i):
          try:
            out_coe=out_coe*self.el_coelist[i]
            self.el_coelist[i]=1
          except IndexError:pass
      res_el,res_coe=self.delete_iota()
      return res_el,res_coe,out_coe

    def include_EP(self):
      res=False
      for i,elem in enumerate(self.ellist):
        gen_query=f'select*from gen where id="{elem}"'
        for row in c.execute(gen_query):
          if '\Delta(' in row['display'] and self.dim_list()[i]-row['n']>0:res=True
      return res

    def is_rep_element(self):
      res=False
      rep_id=None
      rep_coe_li=[0]*12
      del rep_coe_li[HomotopyGroup(self.n,self.k).direct_sum():]
      el_str=' '.join(map(str,self.ellist))
      query_rep_cnt=f'select count( * ) from sphere where n={self.n} and Element="{el_str}"'
      for row in c.execute(query_rep_cnt):
        if row['count( * )']>=1:
          res=True
          query_rep_id=f'select*from sphere where n={self.n} and Element="{el_str}"'
          for row in c.execute(query_rep_id):
            rep_id=int(row['id'])
            rep_coe_li[int(rep_id)]=1
      return res,rep_id,rep_coe_li

    def sus_element(self,totalcoe=1):
      rel_li,ref_li=[],[]
      res_n,res_k=[],[]
      res_sus_rep_coe=[]    
      el_str=' '.join(map(str,self.ellist))
      for i in range(self.desus_max()):
        query_rep_cnt=f'select count( * ) from sphere where n={self.n-i-1} and Element="{el_str}"'
        for row_cnt in c.execute(query_rep_cnt):
          # if row_cnt['count( * )'] >=1:
          if row_cnt['count( * )']<1:continue
          query_rep=f'select*from sphere where n={self.n-i-1} and Element="{el_str}"'
          for row in c.execute(query_rep):
            coe_list=[0]*11
            coe_list.insert(int(row['id']),1)
            for j in range(i+1):
              hg=HomotopyGroup(self.n-i+j,self.k)
              el_lin=ElementLinear(self.n-i+j-1,self.k,coe_list)
              el_lin_E_coe=el_lin.E_coe()
              rep_lin_tex=hg.rep_linear_tex(el_lin_E_coe[0])
              non_zero_li=[i for i in el_lin_E_coe[0] if i!=0]
              if not (len(non_zero_li)==1 and non_zero_li[0]==1):
                if i-j>=2:
                  if self.total_coe==1:rel_li.append(f' E ^{ {i-j} } ({rep_lin_tex} )')
                  else:rel_li.append(f'{self.total_coe} ( E ^{ {i-j} } ({rep_lin_tex} ))')
                elif i-j==1:
                  if self.total_coe==1:rel_li.append(f' E ({rep_lin_tex} )')
                  else:rel_li.append(f'{self.total_coe} ( E ({rep_lin_tex} ))')
                else:rel_li.append(hg.rep_linear_tex(el_lin_E_coe[0], self.total_coe))
                try:ref_li.append(', '.join(el_lin_E_coe[1]))
                except:ref_li.append('')
              res_n=hg.n
              res_k=hg.k
              res_sus_rep_coe.append([coe*self.total_coe for coe in el_lin_E_coe[0]])
              coe_list=el_lin_E_coe[0]
          break
      return rel_li,ref_li,res_n,res_k,res_sus_rep_coe

    def has_relation(self):
      hg=HomotopyGroup(self.n,self.k)
      d_sum=hg.direct_sum()
      res=(False,[],'')
      el_str=' '.join(map(str,self.ellist))
      query_rel_cnt=f'select count( * ) from sphere_relation where n={self.n} and el_str="{el_str}"'
      for row_cnt in c.execute(query_rel_cnt):
        if row_cnt['count( * )']<1:continue
        query_rel=f'select*from sphere_relation where n={self.n} and el_str="{el_str}"'
        for row in c.execute(query_rel):
          res_tot_coe,mod_tot_coe=divmod(self.total_coe,int(row['total_coe']))
          if mod_tot_coe!=0:continue
          row_li=list(map(int,row['rep_coe'].split()))
          rel_rep_coe=[row_li[i]*res_tot_coe for i in range(d_sum)]
          res_ref=row['reference']
          res=(True,rel_rep_coe,res_ref,res_tot_coe)
      return res

    def has_sus_relation(self,totalcoe=1):
      rel_tex_li,ref_tex_li=[],[]
      res_n,res_k=[],[]
      res_rel_rep_coe=[]
      res_tot_coe=self.total_coe
      for i in range(self.desus_max()):
        el=Element(self.n-i-1,self.ellist,self.el_coelist,res_tot_coe)
        el_has_rel=el.has_relation()
        if not el_has_rel[0]:continue
        coe_li=el_has_rel[1]
        res_tot_coe=res_tot_coe//el_has_rel[3]
        res_n.append(el.n)
        res_k.append(el.k)
        res_rel_rep_coe.append(coe_li)
        hg=HomotopyGroup(self.n-i-1,self.k)
        rep_lin_tex_coe_li=hg.rep_linear_tex(coe_li)
        if i>=1:
          if res_tot_coe==1:rel_tex_li.append(f'E^{ {i+1} }({rep_lin_tex_coe_li})')
          else:rel_tex_li.append(f'{res_tot_coe}(E^{ {i+1} }({rep_lin_tex_coe_li}))')
        elif i==0:
          if res_tot_coe==1:rel_tex_li.append(f'E({rep_lin_tex_coe_li})')
          else:rel_tex_li.append(f'{res_tot_coe}(E({rep_lin_tex_coe_li}))')
        else:rel_tex_li.append(hg.rep_linear_tex(coe_li, res_tot_coe))          
        ref_tex_li.append(el_has_rel[2])
        for j in range(i+1):
          hg=HomotopyGroup(self.n-i+j,self.k)
          el_lin=ElementLinear(self.n-i+j-1,self.k,coe_li)
          el_lin_E_coe=el_lin.E_coe()
          rep_lin_tex_el_lin_Ecoe=hg.rep_linear_tex(el_lin_E_coe[0])
          if i-j>=2:
            if res_tot_coe==1:rel_tex_li.append(f'E^{ {i-j} }({rep_lin_tex_el_lin_Ecoe})')
            else:rel_tex_li.append(f'{res_tot_coe}(E^{ {i-j} }({rep_lin_tex_el_lin_Ecoe}))')
          elif i-j==1:
            if res_tot_coe==1:rel_tex_li.append(f'E({rep_lin_tex_el_lin_Ecoe})')
            else:rel_tex_li.append(f'{res_tot_coe}(E({rep_lin_tex_el_lin_Ecoe}))')
          else:rel_tex_li.append(hg.rep_linear_tex(el_lin_E_coe[0], res_tot_coe))
          ref_tex_li.append(', '.join(el_lin_E_coe[1]))
          coe_li=el_lin_E_coe[0]
          res_n.append(el_lin.n+1)
          res_k.append(el_lin.k)
          res_rel_rep_coe.append(coe_li)
        break
      return rel_tex_li,ref_tex_li,res_n,res_k,res_rel_rep_coe,res_tot_coe

    def composition_is_zero(self):
      has_sus_rel=self.has_sus_relation()
      res=False
      rel_tex,ref_tex='',''
      if '0' in has_sus_rel[0]:
        res=True
        rel_tex=has_sus_rel[0][0]
        ref_tex=has_sus_rel[1][0]
      return res,rel_tex,ref_tex

    def element_to_id(self):
      res=False
      el_id=None
      el_li_str=' '.join(list(map(str,self.ellist)))
      query=f'select*from sphere where n={self.n} and Element="{el_li_str}"'
      for row in c.execute(query):
        el_id=int(row['id'])
        res=True
      return res,el_id

    def element_to_linear_coe(self):
      el_to_id=self.element_to_id()
      res=[]
      if el_to_id[0]:
        res=[0]*12 
        res[el_to_id[1]]=1
      return res

    def is_P_image(self):
      elli0=self.ellist
      elem=self.ellist[0]
      gen_query=f'select*from gen where id="{elem}"'
      for row in c.execute(gen_query):
        if '\Delta(' in row['display']:
          res=True
          P_n=row['n']
          P_k=row['k']
          el_P=Element(P_n,[elem])
          res_P_n=2*P_n+1
          res_P_k=P_k-P_n+1
          coe_str=' '.join(list(map(str,el_P.element_to_linear_coe())))
          query=f'select*from sphere where n={res_P_n} and k={res_P_k} and P_coe="{coe_str}"'
          res_el_li=elli0
          for P_row in c.execute(query):
            try:res_el_li=[int(P_row['Element'])]+elli0[1:]
            except ValueError:res_el_li=list(map(int,P_row['Element'].split()))+elli0[1:]
          comp_el_P=Element(P_n,res_el_li)
          comp_el_P_dim_li=comp_el_P.dim_list()
          res_P_k=comp_el_P_dim_li[-1]-comp_el_P_dim_li[0]
        else:res,res_P_n,res_P_k,res_el_li=False,0,0,elli0
      return res,res_P_n,res_P_k,res_el_li

    def el_dim_list(self):
# 表示元の境目の次元のリストを与えるメソッド
      res=[self.n]
      for i,elem in enumerate(self.ellist):
        gen_query=f'select * from gen where id = "{elem}" '
        for row in c.execute(gen_query):
          res.append(res[i]+row['k'])
      return res

    def sub_comp(self,i,j):
      sub_el_list=self.ellist[i:i+j]
      sub_el_coe_list=self.el_coelist[i:i+j]
      return sub_el_list,sub_el_coe_list 

    def total_coe_to_sub_comp(self,i,j):
      res=False
      suslist=self.sus_list()[i+j+1:]
      suslist.append(self.dim_list()[-1])
      if min(suslist)>=1:res = True
      return res

    def sub_comp_list(self,t):
      el_li=self.ellist
      el_coe_li=self.el_coelist
      el_dim_li=self.el_dim_list()
      subli_n=[]
      subli_k=[]
      subli_el=[]
      subli_el_coe=[]
      bin_t=bin(t)[2:]
      bin_t0='0'*(len(el_li)-1-len(bin_t))+bin_t+'1'
      j=1
      for i in range(len(el_li)):
        if i==0:subli_n.append(el_dim_li[0])
        elif bin_t0[i-1]=='1':subli_n.append(el_dim_li[i])
        if bin_t0[i]=='1':
          sub_comp=self.sub_comp(i-j+1,j)
          subli_el.append(sub_comp[0])
          subli_el_coe.append(sub_comp[1])
          j=1
        else:j+=1
      for i in range(len(subli_n)):
        if i<=len(subli_n)-2:subli_k.append(subli_n[i+1]-subli_n[i])
        else:subli_k.append(el_dim_li[-1]-subli_n[-1])
      return subli_n,subli_k,subli_el,subli_el_coe

    def sub_comp_tex_list(self,t):
      sub_li=self.sub_comp_list(t)
      res=[]
      for i in range(len(sub_li[0])):
        sub_n=sub_li[0][i]
        sub_k=sub_li[1][i]
        sub_el_li=sub_li[2][i]
        sub_el_coe_li=sub_li[3][i]
        sub_hg=HomotopyGroup(sub_n,sub_k)
        res.append(sub_hg.el_coe_tex(sub_el_li,sub_el_coe_li))
      return res

    def change_el_list_list(self,i_li,j_li,sub_ellili,sub_el_coelili):
      res_el=[e for e in self.ellist]
      res_coe=[c for c in self.el_coelist]
      for ni in reversed(range(len(res_el))):
        if ni in i_li:
          i=i_li.index(ni)
          nj=j_li[i]
          res_el[ni:ni+nj]=sub_ellili[i]
          res_coe[ni:ni+nj]=sub_el_coelili[i]
      return res_el,res_coe

    def include_zero_subcomp(self):
      res=False
      res_rel=[]
      res_ref=[]
      for t in range(2**(len(self.ellist)-1)):
        (t_n_li,t_k_li,t_el_li,t_el_coe_li)=self.sub_comp_list(t)
        for i in range(len(t_n_li)):
          t_i_hg=HomotopyGroup(t_n_li[i],t_k_li[i])
          t_i_el=Element(t_n_li[i],t_el_li[i],t_el_coe_li[i])
          t_i_el_is_zero=t_i_el.composition_is_zero()
          if t_i_hg.group_is_zero():
            res=True
            res_rel.append('0')
            el_tex=t_i_el.tex()
            res_ref.append(f'{el_tex} \in\pi_{ {t_n_li[i] + t_k_li[i]} }^{ {t_n_li[i]} }=0')
          if t_i_el_is_zero and t_i_el_is_zero[1]!='':
            res=True
            res_rel.append('0')
            res_ref.append(t_i_el_is_zero[2])
      return res,res_rel,res_ref

    def element_order(self):
      is_rep_el=self.is_rep_element()
      sus_el=self.sus_element()
      has_rel=self.has_relation()
      has_sus_rel=self.has_sus_relation()
      res=None
      rep_coe_li=[]
      if is_rep_el[0]:rep_coe_li=is_rep_el[2]
      elif sus_el[4]!=[]:rep_coe_li=sus_el[4][-1]
      elif has_rel[0]:rep_coe_li=has_rel[1]
      elif has_sus_rel[4]!=[]:rep_coe_li=has_sus_rel[4][-1]
      if rep_coe_li!=[]:
        el_lin=ElementLinear(self.n,self.k,rep_coe_li)
        res=el_lin.rep_linear_order()
      return res

    def make_sub_ellist_list(self,t_n,t_k,t_el,dim_li_idx_ii):
      i_li,j_li=[],[]
      sub_ellili=[]
      sub_el_coelili=[]
      res_sub_ref_li=[]
      break_flg=False

      if self.is_rep_element()[0]==False:

        t_i_el_sus_el=self.sus_element()
        t_i_el_has_rel=self.has_relation()

        if t_el==[1]:pass
        elif t_i_el_sus_el[4]!=[]:
          # print(f'sus_element = {t_i_el_sus_element[4]}')
          if t_i_el_sus_el[1]!=[]:res_sub_ref_li.append(', \ '.join(t_i_el_sus_el[1]))
          else:res_sub_ref_li.append('')
          sub_rep_coe=t_i_el_sus_el[4][-1]
          sub_el_lin=ElementLinear(t_n,t_k,sub_rep_coe)
          sub_el_lin_to_el_li=sub_el_lin.linear_to_el_list()

          if sub_el_lin_to_el_li[0]==[]:break_flg=True
          i_li.append(dim_li_idx_ii)
          j_li.append(len(t_el))
          sub_ellili.append(sub_el_lin_to_el_li[0])
          sub_el_coelili.append(sub_el_lin_to_el_li[1])
            
        elif t_i_el_has_rel[0]:
          sub_rep_coe=t_i_el_has_rel[1]
          res_sub_ref_li.append(t_i_el_has_rel[2])
          sub_el_lin=ElementLinear(t_n, t_k, sub_rep_coe)
          sub_el_lin_to_el_li=sub_el_lin.linear_to_el_list()

          if sub_el_lin_to_el_li[0]==[]:break_flg=True
          i_li.append(dim_li_idx_ii)
          j_li.append(len(t_el))
          sub_ellili.append(sub_el_lin_to_el_li[0])
          sub_el_coelili.append(sub_el_lin_to_el_li[1])

      return i_li,j_li,sub_ellili,sub_el_coelili,res_sub_ref_li,break_flg

    def total_coe_times_sub_comp(self):
      res_sub_tex,res_sub_ref,res_coe= [],[],[]

#########################################################
# 係数を外へ出して、そのelementをel2とする
      elli2,rep_coe_li2,tot_coe2= self.el_coe_out()
      el2=Element(self.n,elli2,rep_coe_li2,tot_coe2)
      el2_el_to_lin_coe=el2.element_to_linear_coe()
      el2_dim_li=el2.dim_list()
      if el2_el_to_lin_coe!=[]:
# 生成元のlinearであれば、それからtexに変換
        hg2=HomotopyGroup(self.n,self.k)
        res_sub_tex.append(hg2.rep_linear_tex(el2_el_to_lin_coe,tot_coe2))
# 生成元でなければ、elementからtexに変換
      else:res_sub_tex.append(el2.tex())
#########################################################

      if tot_coe2>=2:
        # if el2.el_dim_list()[i] in [3,7]:
        #   pass
        # else:
        # el1_el_coe_out = self.el_coe_out()
# tot_coe2>=2のとき(2.1)をreferenceに追加、そうでなければtexを削除
        res_sub_ref.append('(2.1), \ k(\\alpha\\beta)=\\alpha(k\\beta)' 
            + ', \ k(\\alpha E \\beta)=(k\\alpha) E \\beta'
            + ', \ \ Lem4.5, \ (k\iota_{n-1})\\beta = k\\beta \ for \ \\beta \in \pi_{i-1}(S^{n-1})'
            + ', \ n = 2, 4, 8' )
      else:res_sub_tex.pop(-1)

      is_zero=False
      for i in range(len(elli2)):
        for j in range(1,len(elli2)-i+1):
          elli3,rep_coe_li3=el2.sub_comp(i,j)
          n3=el2_dim_li[i]
          k3=el2_dim_li[i+j]-el2_dim_li[i]
# n3,k3:sub_comp(i,j)のn,k
          sub_el3=Element(n3,elli3,rep_coe_li3)
          sub_el3_tot_coe_to_sub_comp_ij= sub_el3.total_coe_to_sub_comp(i,j)
# sub_el3_tot_coe_to_sub_comp_ij:sub_comp(i,j)にtot_coeを掛けられるかどうか
          sub_el3_el_ord=sub_el3.element_order()
          sub_el3_tex=sub_el3.tex()
          sub_hg3=HomotopyGroup(n3,k3)
          sub_hg3_gr_ord=sub_hg3.group_order()

          try:
            if sub_el3_tot_coe_to_sub_comp_ij and tot_coe2%sub_el3_el_ord==0:
# tot_coe2がsub_comp(i,j)のorderの倍数のとき
              res_sub_tex.append('0')
              if sub_el3_el_ord==1:res_sub_ref.append(f'{sub_el3_tex} = 0')
              else:res_sub_ref.append(f'{sub_el3_el_ord} {sub_el3_tex} = 0')
          except:pass
          try:
            if sub_el3_tot_coe_to_sub_comp_ij and tot_coe2%sub_hg3_gr_ord==0:
# tot_coe2がsub_comp(i,j)を含む群のorderの倍数のとき
              res_sub_tex.append('0')
              res_sub_ref.append(f'{sub_hg3_gr_ord} \pi_{ {n3}+{k3} }^{n3} = 0')
            else:pass
          except:pass
          if len(res_sub_tex)>=2:
            try:
              if res_sub_tex[-1]==res_sub_tex[-2]:
# res_sub_texがかぶっている場合は削除する
                res_sub_tex.pop(-1)
                res_sub_ref.pop(-1)
            except IndexError:pass
          if '0' in res_sub_tex:
# 結果が0になる場合
            hg = HomotopyGroup(self.n,self.k)
            res_coe=[0]*hg.direct_sum()              
            is_zero=True
            break
        if is_zero:break
      return res_sub_tex,res_sub_ref,res_coe,is_zero

    def total_coe_times_sub_comp_is_zero(self,totalcoe=1):
      res_sub_tex,res_sub_ref,res_coe= [],[],[]
      is_zero=False
      for t in range(1<<(len(self.ellist)-1)):
# 合成の境目をビット全探索
        tn_li, tk_li, tel_li, tel_coe_li= self.sub_comp_list(t)
        i_li,j_li=[],[]
        sub_ellili,sub_el_coelili= [],[]
        for ti,(tn,tk,tel,tel_coe) in enumerate(zip(tn_li,tk_li,tel_li,tel_coe_li)):
          dim_li_idx_ti= self.dim_list().index(tn_li[ti])
          ti_el= Element(tn,tel,tel_coe)
# ti_el: 各tiに対応するelement
          ti_el_sub= ti_el.make_sub_ellist_list(tn,tk,tel,dim_li_idx_ti)
          i_li.extend(ti_el_sub[0])
          j_li.extend(ti_el_sub[1])
          sub_ellili.extend(ti_el_sub[2])
          sub_el_coelili.extend(ti_el_sub[3])
          res_sub_ref.extend(ti_el_sub[4])
          break_flg=ti_el_sub[5]
          if break_flg: break
        elli1,el_coeli1= self.change_el_list_list(i_li,j_li,sub_ellili,sub_el_coelili)
        el1= Element(self.n,elli1,el_coeli1,totalcoe)
# el1: tの場合の結果のelement
        if i_li!=[]: res_sub_tex.append(el1.tex())
        res=el1.total_coe_times_sub_comp()
        res_sub_tex.extend(res[0])
        res_sub_ref.extend(res[1])
        res_coe.extend(res[2])
        is_zero=res[3]
        if is_zero: break        
      return res_sub_tex,res_sub_ref,res_coe

    def change_first_dim(self,fst_dim):
      n=self.n
      dim_li=self.dim_list()
      if fst_dim=='first_element' or len(dim_li)==1:
        gen_query=f'select*from gen where id={self.ellist[0]}'
        c.execute(gen_query)
        n=c.fetchone()['n']
      elif fst_dim=='second_element':
        try:
          gen_query=f'select*from gen where id={self.ellist[1]}'
          for row in c.execute(gen_query):
            n=dim_li[0]-dim_li[1]+row['n']
        except IndexError:
          gen_query=f'select*from gen where id={self.ellist[0]}'
          c.execute(gen_query)
          n=c.fetchone()['n']
      return n

    def deformation_relation(self,coe_li0=[1]*12):
      hg=HomotopyGroup(self.n,self.k)
      hg_is_zero=hg.group_is_zero()
      hg_dsum=hg.direct_sum()
      rel_tex_li=[]
      ref_tex_li=[]
      res_coe_li=[]
      el_li1=[el for el in self.ellist]
      coe_li1=[coe for coe in self.el_coelist]
      selfelli,selfel_coeli,selftot_coe=hg.el_coe_out(el_li1,coe_li1)
      selftot_coe*=self.total_coe
      
      coeout_el=Element(self.n,selfelli,selfel_coeli,selftot_coe)
      # coeout_el = Element(self.n, selfellist, selfel_coelist, 1)
      coeout_is_rep=coeout_el.is_rep_element()
      coeout_el_in_EP=coeout_el.include_EP()
      coeout_el_has_rel=coeout_el.has_relation()
      coeout_el_has_sus_rel_tot_coe=coeout_el.has_sus_relation(selftot_coe)
      # if selfellist != []:
      coeout_el_is_P=coeout_el.is_P_image()

# case with elemets include zero
      if 0 in selfelli:
        rel_tex_li.append('0')
        ref_tex_li.append('')
        res_coe_li=[0]*hg_dsum

# case with group is zero
      elif hg_is_zero:
        rel_tex_li.append('0')
        ref_tex_li.append(f'\pi_{ {self.n+self.k} }^{ {self.n} }=0')
        res_coe_li=[0]*hg_dsum

# case with representation element
      elif hg_is_zero==False and coeout_is_rep[0]:
        rel_tex_li.append(hg.rep_linear_tex(coeout_is_rep[2],selftot_coe))
        gencoe_li=[coe*self.total_coe for coe in coeout_is_rep[2]]
        res_coe_li=hg.mod_gen_coe_list(gencoe_li)
        ref_tex_li.append(f'(Generator)')

# case with include EP
      elif coeout_el_in_EP:
        rel_tex_li.append('0')
        ref_tex_li.append(' E P=0')
        res_coe_li=[0 for _ in range(hg_dsum)]

      # if reference_tex_list == []:
# case with relation
      if coeout_el_has_rel[0] and res_coe_li==[]:
        # print('coeout_el_has_relation')
        # print(f'coeout_el_has_relation {coeout_el_has_relation[1]}, {selftotal_coe}')
        selftot_coe=selftot_coe//coeout_el_has_rel[3]
        hg_rep_lin_tex_coeout_el_has_rel_totcoe=hg.rep_linear_tex(coeout_el_has_rel[1],selftot_coe)
        # print(hg_rep_linear_tex_coeout_el_has_relation_selftotal_coe)
        if hg_rep_lin_tex_coeout_el_has_rel_totcoe not in rel_tex_li or coeout_el_has_rel[2] not in ref_tex_li:
          # print(f'coeout_el_has_relation {coeout_el_has_relation}, {selftotal_coe}')
          rel_tex_li.append(hg_rep_lin_tex_coeout_el_has_rel_totcoe)
          # print([coe * selftotal_coe for coe in coeout_el_has_relation[1]])
          ref_tex_li.append(coeout_el_has_rel[2])
          res_coe_li=[coe*selftot_coe for coe in coeout_el_has_rel[1]]

# case with suspension of relation 
      if hg_is_zero==False and coeout_el_in_EP==False and '0' not in rel_tex_li and res_coe_li==[]:
        for relation,reference in zip(coeout_el_has_sus_rel_tot_coe[0],coeout_el_has_sus_rel_tot_coe[1]):
          if relation not in rel_tex_li or reference not in ref_tex_li:
            rel_tex_li.append(relation)
            ref_tex_li.append(reference)
            res_coe_li = coeout_el_has_sus_rel_tot_coe[4][-1]
        # relation_tex_list.extend(el.has_sus_relation(total_coe)[0])
        # reference_tex_list.extend(el.has_sus_relation(total_coe)[1])

# case with group include subcomposition is zero
      elif hg_is_zero==False and coeout_el_in_EP==False and len(selfelli)>=2:
        for t in range(2**(len(selfelli)-1)):
          t_n_li,t_k_li,t_el_li,_=hg.sub_comp_list(selfelli,selfel_coeli,t)
          for i in range(len(t_n_li)):
            t_i_hg=HomotopyGroup(t_n_li[i], t_k_li[i])
            t_i_el=Element(t_n_li[i],t_el_li[i])
            t_i_el_is_zero=t_i_el.composition_is_zero()
            if t_i_hg.group_is_zero():
              rel_tex_li.append('0')
              el_tex=t_i_el.tex()
              ref_tex_li.append(f'{el_tex} \in \pi_{ {t_n_li[i]+t_k_li[i]} }^{ {t_n_li[i]} }=0')
              res_coe_li=[0 for _ in range(hg_dsum)]
            if t_i_el_is_zero and t_i_el_is_zero[1]!='':
              # relation_tex_list.append(t_i_el_composition_is_zero[1])
              rel_tex_li.append(f'0')
              # el_tex = t_i_el.tex()
              ref_tex_li.append(t_i_el_is_zero[2])
              # reference_tex_list.append('')
              res_coe_li=[0 for _ in range(hg_dsum)]

# case with suspension of representation element
      # print(self_sus_element_selftotal_coe[0])
      if hg_is_zero==False and coeout_el_in_EP==False and '0' not in rel_tex_li and res_coe_li==[]:
        # print('sus of rep', selfellist, selfel_coelist, selftotal_coe)
        coeout_el_sus_el_totcoe=coeout_el.sus_element(selftot_coe)
        # coeout_el_sus_element_selftotal_coe = coeout_el.sus_element(2)
        for relation,reference in zip(coeout_el_sus_el_totcoe[0],coeout_el_sus_el_totcoe[1]):
          # print(relation)
          if relation not in rel_tex_li or reference not in ref_tex_li:
            rel_tex_li.append(relation)
            # reference_tex_list.append(reference + f'{coeout_el_sus_element_selftotal_coe[4][-1]}')
            ref_tex_li.append(reference)
            res_coe_li=coeout_el_sus_el_totcoe[4][-1]
            # return_coe_list = [1,0]
            # print(f'return_coe_list = {return_coe_list}')
            # gencoe_list = [coe * total_coe for coe in self.is_rep_element()[2]]
            # return_coe_list = hg.mod_gen_coe_list(gencoe_list)

            # relation_tex_list.extend(el.sus_element(total_coe)[0])
            # reference_tex_list.extend(el.sus_element(total_coe)[1])

      # print(f'el_list = {el_list}, {coe_list}')

# case with P-image
      if selfelli!=[]:
        if coeout_el_is_P[0] and len(selfelli)>=2:
          # print('coeout_el_is_P_image')
          if len(coeout_el_is_P[3])>len(selfel_coeli):coe_list=[1]*(len(coeout_el_is_P[3])-len(selfel_coeli))+selfel_coeli
          else:coe_list=selfel_coeli

          Ptot_coe=np.prod(coe_li0)
          Pinv_n=coeout_el_is_P[1]
          Pinv_k=coeout_el_is_P[2]
          Pinv_el_li=hg.delete_iota(coeout_el_is_P[3],coe_list)[0]
          Pinv_hg=HomotopyGroup(Pinv_n,Pinv_k)
          Pinv_el=Element(Pinv_n,Pinv_el_li)
          Pinv_el_to_id=Pinv_el.element_to_id()
          Pinv_hg_Pcoe_Pinv_el_to_id=Pinv_hg.P_coe(Pinv_el_to_id[1])
          P_image_coe=Pinv_hg_Pcoe_Pinv_el_to_id[0]
          Pinv_el_tex=Pinv_el.tex()
          if Ptot_coe==1:
            rel_tex_li.append(f'\Delta( {Pinv_el_tex} )')
            res_coe_li=P_image_coe
          else:
            rel_tex_li.append(f'{Ptot_coe} \Delta( {Pinv_el_tex} )')
            res_coe_li=[i*self.total_coe for i in P_image_coe]
          
          ref_tex_li.append('Prop2.5, \ \Delta(\\alpha E ^2 \\beta)=\Delta(\\alpha)\\beta')
          # if P_inverse_hg_P_coe_P_inverse_el_element_to_id[1] != None:
          rel_tex_li.append(hg.rep_linear_tex(P_image_coe,Ptot_coe))
          # print(relation_tex_list)
          ref_tex_li.append(Pinv_hg_Pcoe_Pinv_el_to_id[1])
          # return_coe_list = []
    
# case with total_coe_times_sub_comp_is_zero
        if ref_tex_li==[] and res_coe_li==[]:
          if '0' not in rel_tex_li:
            # print('total_coe_times_sub_comp_is_zero')
            coeout_el_totcoe_times_sub_is_zero_totcoe=coeout_el.total_coe_times_sub_comp_is_zero(selftot_coe)
            rel_tex_li.extend(coeout_el_totcoe_times_sub_is_zero_totcoe[0])
            ref_tex_li.extend(coeout_el_totcoe_times_sub_is_zero_totcoe[1])
            res_coe_li=coeout_el_totcoe_times_sub_is_zero_totcoe[2]

      else:rel_tex_li.append(f'{selftot_coe} \iota_{n}')

      return rel_tex_li,ref_tex_li,res_coe_li

    def el_split(self,symbols0):
      split_el_lili=[]
      split_coe_lili=[]
      split_el_li=[]
      split_coe_li=[]
      for el, coe, symbol in zip(self.ellist, self.el_coelist, symbols0):
        if symbol == '+':
          split_el_lili.append(split_el_li)
          split_coe_lili.append(split_coe_li)
          split_el_li = [el]
          split_coe_li = [coe]
        else:
          split_el_li.append(el)
          split_coe_li.append(coe)
      split_el_lili.append(split_el_li)
      split_coe_lili.append(split_coe_li)
      # print(f'split_el_list_list, split_coe_list_list = {split_el_list_list, split_coe_list_list}')
      return split_el_lili, split_coe_lili

    def distributive_split(self, symbols0):

      symbols0_0 = symbols0[0]
      symbols0_1 = symbols0[-1]

      if '(' not in symbols0:
        symbols0[0] = '('
        symbols0[-1] = ')'

      bra_el_lili = [[], [], []]
      bra_coe_lili = [[], [], []]
      bra_symbol_lili = [[], [], []]
      dis_el_lili = []
      dis_coe_lili = []

      self_elli = [el for el in self.ellist]
      self_el_coeli = [coe for coe in self.el_coelist]
      self_symbols = [symbol for symbol in symbols0]

      bra_idx0 = symbols0.index('(')
      bra_idx1 = symbols0.index(')')

      bra_el_lili[0] = self_elli[:bra_idx0]
      bra_el_lili[1] = self_elli[bra_idx0:bra_idx1]
      bra_el_lili[2] = self_elli[bra_idx1:]
      bra_coe_lili[0] = self_el_coeli[:bra_idx0]
      bra_coe_lili[1] = self_el_coeli[bra_idx0:bra_idx1]
      bra_coe_lili[2] = self_el_coeli[bra_idx1:]
      bra_symbol_lili[0] = self_symbols[:bra_idx0]
      bra_symbol_lili[1] = self_symbols[bra_idx0:bra_idx1]
      bra_symbol_lili[2] = self_symbols[bra_idx1:]

      # print(f'bracket_el_list_list = {bracket_el_list_list, bracket_coe_list_list, bracket_symbol_list_list}')

      bra_dim = self.dim_list()[bra_idx0]
      bra_el = Element(bra_dim, bra_el_lili[1], bra_coe_lili[1])
      (bra_split_el_lili, bra_split_coe_lili) = bra_el.el_split(bra_symbol_lili[1])

      # print(f'bracket_split_el_list_list = {bracket_split_el_list_list, bracket_split_coe_list_list}')

      for bra_split_el, bra_split_coe in zip(bra_split_el_lili, bra_split_coe_lili):
        dis_el_li = [el for el in bra_el_lili[0]]
        dis_el_li.extend(bra_split_el)
        dis_el_li2 = [el for el in bra_el_lili[2]]
        dis_el_li.extend(dis_el_li2)
        dis_el_lili.append(dis_el_li)
        dis_coe_list = [coe for coe in bra_coe_lili[0]]
        dis_coe_list.extend(bra_split_coe)
        dis_coe_li2 = [coe for coe in bra_coe_lili[2]]
        dis_coe_list.extend(dis_coe_li2)
        dis_coe_lili.append(dis_coe_list)

      # print(f'distributive_el_list_list = {distributive_el_list_list, distributive_coe_list_list}')

      symbols0[0] = symbols0_0
      symbols0[-1] = symbols0_1

      return bra_el_lili, bra_coe_lili, bra_symbol_lili, \
        dis_el_lili, dis_coe_lili

    def el_sum(self, symbols0):
      # (split_el_list_list, split_coe_list_list) = self.el_split(symbols0)
      # print(f'split_coe_list_list = {split_coe_list_list[0]}')
      # el_list0_0 = split_el_list_list[0]
      # el_list0_1 = split_el_list_list[1]
      # coe_list0_0 = split_coe_list_list[0]
      # coe_list0_1 = split_coe_list_list[1]

      # bra_el_list_list, bra_coe_list_list, bra_symbol_list_list, split_el_list_list, split_coe_list_list = self.distributive_split(symbols0)
      _,_,_, split_el_lili, split_coe_lili = self.distributive_split(symbols0)
      # (bra_el_list_list, bra_coe_list_list, bra_symbol_list_list, \
      #   distri_el_list_list, distri_coe_list_list) = self.distributive_split(symbols0)

      el0_0 = Element(self.n, split_el_lili[0], split_coe_lili[0])
      # el0_1 = Element(self.n, el_list0_1)

      hg = HomotopyGroup(self.n, el0_0.k)

      el_list2 = []
      coe_list2 = []
      tocoe_list2 = []
      rel_tex_li2 = []
      ref_tex_li2 = []
      res_coe_li2 = []
      len_list = []
      for i, (split_el_li, split_coe_li) in enumerate(zip(split_el_lili,split_coe_lili)):
        (elem1, coe1) = hg.delete_iota(split_el_li, split_coe_li)
      
        (elem2, coe2, tot_coe2) = hg.el_coe_out(elem1, coe1)
        el2 = Element(self.n, elem2, coe2, tot_coe2)
        (rel_tex0, ref_tex0, res_coe0) = el2.deformation_relation(coe2)
        rel_tex_li2.append(rel_tex0)
        ref_tex_li2.append(ref_tex0)
        res_coe_li2.append(res_coe0)
        len_list.append(len(rel_tex0))

        el_list2.append(elem2)
        coe_list2.append(coe2)
        tocoe_list2.append(tot_coe2)
      # print(f'relation_tex_list2 = {relation_tex_list2, reference_tex_list2, return_coe_list2, len_list}')
      max_len2 = max(len_list)

      for i in range(len(rel_tex_li2)):
        # print(relation_tex_list2)
        if len(rel_tex_li2[i]) < max_len2:
          # print(relation_tex_list2)
          rel_add_li = [rel_tex_li2[i][-1]] * (max_len2 - len(rel_tex_li2[i]))
          ref_add_li = [ref_tex_li2[i][-1]] * (max_len2 - len(rel_tex_li2[i]))
          rel_tex_li2[i].extend(rel_add_li)
          ref_tex_li2[i].extend(ref_add_li)

      res_rel = []
      res_ref = []
      for j in range(max_len2): # 0-4
        for i in range(len(rel_tex_li2)): # 0-2
          if i == 0:
            rel_sum = rel_tex_li2[i][j]
            try:ref_sum = ref_tex_li2[i][j]
            except:ref_sum = ''         
          else:
            rel_sum = rel_sum + '+' + rel_tex_li2[i][j]
            ref_sum = ref_sum + ' , ' + ref_tex_li2[i][j]
        res_rel.append(rel_sum)
        res_ref.append(ref_sum)

      res_coe_li = []
      hg_dsum = hg.direct_sum()
      # print(f'return_coe_list2 = {return_coe_list2}')
      if [] not in res_coe_li2:
        for i in range(hg_dsum):
          last_coe_sum = []
          for last_coe_list in res_coe_li2:last_coe_sum.append(int(last_coe_list[i]))
          res_coe_li.append(sum(last_coe_sum))
        res_rel.append(hg.rep_linear_tex(res_coe_li))
      else:res_rel.append('?')

      return res_rel, res_ref


  class WhiteheadProduct:
    def __init__(self,n,symbollist,ellist=[1],coelist=[1]*6):
      self.n=n
      self.symbollist=symbollist
      self.ellist=ellist
      self.coelist=coelist[:len(ellist)]

    def ellist_to_wp_ellist(self):
      res=[[],[],[],[]]
      j=0
      for i,elem in enumerate(self.ellist):
        if self.symbollist[i]==' ': res[j].append(elem)
        else: j+=1; res[j].append(elem)
      return res

    def coelist_to_wp_coelist(self):
      res=[[],[],[],[]]
      j=0
      for i,coe in enumerate(self.coelist):
        if self.symbollist[i]==' ':res[j].append(coe)
        else: j+=1; res[j].append(coe)
      return res

    def wp_k(self):
      wp_ellist=self.ellist_to_wp_ellist()
      res=n+k_dim(wp_ellist[0])+k_dim(self.ellist)-1
      return res

    def wp_dim_list(self):
      res=[]
      wp_ellist=self.ellist_to_wp_ellist()
      for j in range(6):
        if j==0:res.append(self.n)
        elif j==1:
          el=Element(self.n, wp_ellist[0])
          res.append(res[0]+el.k)
        elif j==2 or j==3:
          if len(wp_ellist)<j: res.append(res[1])
          else:
            el=Element(res[j-1],wp_ellist[j-1])
            res.append(res[1]+el.k)
        elif j==4: res.append(res[2]+res[3]-1)
        else:
          wp_k=self.wp_k()
          res.append(self.n+wp_k)
      return res

    def tex(self):
      res=''
      wp_dim_li=self.wp_dim_list()
      wp_elli=self.ellist_to_wp_ellist()
      wp_coeli=self.coelist_to_wp_coelist()
      for j in range(4):
        if j==1: res+=' [ '
        elif j==2: res+=', '
        elif j==3: res+=' ] '
        if j==0 or j==1: el=Element(wp_dim_li[j],wp_elli[j],wp_coeli[j])
        elif j==2: el=Element(wp_dim_li[1],wp_elli[2],wp_coeli[2])
        else: el=Element(wp_dim_li[4],wp_elli[3],wp_coeli[3])
        res+=el.tex()
      return res

    def wp_ellist_to_ellist(self):
      res_el=[]
      res_coe=[]
      wp_elli=self.ellist_to_wp_ellist()
      wp_coeli=self.coelist_to_wp_coelist()
      wp_dim_li=self.wp_dim_list()
      P_dict={6:5,10:13,12:17,14:22,16:31,18:41,20:53,21:66,22:68,24:87,26:116,28:143,30:164,32:195}
      if wp_dim_li[1] in P_dict:
        res_el=wp_elli[0]
        res_coe=wp_coeli[0]
        res_el.append(P_dict[wp_dim_li[1]])
        res_coe.append(1)
        for i in range(1,4):
          res_el.extend(wp_elli[i])
          res_coe.extend(wp_coeli[i])
      return res_el,res_coe


  class TodaBracket: 
    def __init__(self,n,tt,symbollist,ellist=[1],coelist=[1]*6):
      self.n=n
      self.tt=tt
      self.symbollist=symbollist
      self.ellist=ellist
      self.coelist=coelist[:len(ellist)]
      self.k=k_dim(ellist)+1

    def included_group(self):
      return 

    def ellist_to_tb_ellist(self):
      if self.symbollist.count(',')==2: res=[[],[],[],[],[]]
      elif self.symbollist.count(',')==3: res=[[],[],[],[],[],[]]
      j=0
      for i,elem in enumerate(self.ellist):
        if self.symbollist[i]==' ' or self.symbollist[i]=='+': res[j].append(elem)
        else: j+=1; res[j].append(elem)
      return res

    def coelist_to_tb_coelist(self):
      if self.symbollist.count(',')==2: res=[[],[],[],[],[]]
      elif self.symbollist.count(',')==3: res=[[],[],[],[],[],[]]
      j=0
      for i,coe in enumerate(self.coelist):
        if self.symbollist[i]==' ' or self.symbollist[i]=='+': res[j].append(coe)
        else: j+=1; res[j].append(coe)
      return res

    def symbollist_to_tb_symbollist(self):
      self_symli=self.symbollist
      bra1_idx=self_symli.index('{')
      bra2_idx=self_symli.index('}')
      tb_symli0=[symbol for i,symbol in enumerate(self_symli) if bra1_idx<=i and i<=bra2_idx]
      comma_idx1=tb_symli0.index(',')
      tb_symli0[comma_idx1]='('
      comma_idx2=tb_symli0.index(',')
      tb_symli0[comma_idx2]=')'
      tb_symli0[0]=' '
      tb_symli0[-1]=' '
      if self.symbollist.count(',')==2: res=[[],[]]
      elif self.symbollist.count(',')==3: res=[[],[],[]]
      res[0]=[sym for i,sym in enumerate(tb_symli0) if i<=comma_idx2]
      res[1]=[sym for i,sym in enumerate(tb_symli0) if i>=comma_idx1]
      tb_symli2=[sym for i,sym in enumerate(tb_symli0) if i>=comma_idx1 and i<=comma_idx2]
      res.append(tb_symli2)
      return res

    def tb_el_cnt_list(self):
      return [len(self.ellist_to_tb_ellist()[i]) for i in range(5)]

    def tb_dim_list(self):
      res=[]
      tb_ellist=self.ellist_to_tb_ellist()
      if self.symbollist.count(',')==2:
        if '+' not in self.symbollist:
          for j in range(6):
            el=Element(self.n,tb_ellist[j-1])
            el_dim_li=el.el_dim_list()
            if j==0: res.append(self.n)
            elif j<=3 or j==5: res.append(res[j-1]+el_dim_li[-1]-el_dim_li[0])
            else: res.append(res[j-1]+el_dim_li[-1]-el_dim_li[0]+1)
        else:
          for j in range(6):
            if self.symbollist[j-1]=='+':
              tb_elli_j1=[el for el in tb_ellist[j-1]]
              tb_sym_li_mid =self.symbollist_to_tb_symbollist()[2]
              del tb_elli_j1[tb_sym_li_mid.index('+'):]
              el=Element(self.n,tb_elli_j1)
              el_dim_li=el.el_dim_list()
              if j==0: res.append(self.n)
              elif j<=3 or j==5: res.append(res[-1]+el_dim_li[-1]-el_dim_li[0])
              else: res.append(res[-1]+el_dim_li[-1]-el_dim_li[0]+1)
            else:
              el=Element(self.n,tb_ellist[j-1])
              el_dim_li=el.el_dim_list()
              if j==0: res.append(self.n)
              elif j<=3 or j==5: res.append(res[-1]+el_dim_li[-1]-el_dim_li[0])
              else: res.append(res[-1]+el_dim_li[-1]-el_dim_li[0]+1)
      elif self.symbollist.count(',')==3:
        for j in range(7):
          el=Element(self.n,tb_ellist[j-1])
          el_dim_li=el.el_dim_list()
          if j==0: res.append(self.n)
          elif j<=4 or j==6: res.append(res[j-1]+el_dim_li[-1]-el_dim_li[0])
          else: res.append(res[j-1]+el_dim_li[-1]-el_dim_li[0]+1)
      return res

    def tb_ellist_to_ellist_str(self):
      elli_str_li=[]
      elli_to_tb_elli=self.ellist_to_tb_ellist()
      if self.symbollist.count(',')==2:
        for i in range(1,4):
          if '+' in self.symbollist: elli_to_tb_elli[2]=[' + '.join(map(str,elli_to_tb_elli[2]))]
          elli_str_li.append(' '.join(map(str,elli_to_tb_elli[i])))
      elif self.symbollist.count(',')==3:
        for i in range(1,5): elli_str_li.append(' '.join(map(str, elli_to_tb_elli[i])))
      return ' , '.join(elli_str_li)

    def tb_coelist_to_coelist_str(self):
      coeli_str_li=[]
      if self.symbollist.count(',')==2:
        for i in range(1,4): coeli_str_li.append(' '.join(map(str, self.coelist_to_tb_coelist()[i])))
      elif self.symbollist.count(',')==3:
        for i in range(1,5): coeli_str_li.append(' '.join(map(str, self.coelist_to_tb_coelist()[i])))
      return ' , '.join(coeli_str_li)

    def include_element_list(self):
      res=[]
      res_ref=''
      ellist_str=self.tb_ellist_to_ellist_str()
      coelist_str=self.tb_coelist_to_coelist_str()
      query_tb_cnt=f'select count( * ) from TBtable where element="{ellist_str}" and coefficient="{coelist_str}"'
      for row in c.execute(query_tb_cnt):
        if row['count( * )']>=1:
          query_tb=f'select*from TBtable where element="{ellist_str}" and coefficient="{coelist_str}"'
          for row_tb in c.execute(query_tb):
            if self.n>=row_tb['n'] and self.tt<=row_tb['tt']+self.n-row_tb['n']:
              res=list(map(int, row_tb['include'].split()))
              res_ref=row_tb['reference']
      return res,res_ref

    def tex(self):
      res=''
      tb_dim_li=self.tb_dim_list()
      tb_elli=self.ellist_to_tb_ellist()
      tb_coeli=self.coelist_to_tb_coelist()
      tb_symli=self.symbollist_to_tb_symbollist()
      if self.symbollist.count(',')==2:
        for j in range(5):
          if j==1: res+=' \{ '
          elif j==2 or j==3: res+=', '
          elif j==4:
            if tt==0: res+=' \} '
            else: res+=' \}_{'+f'{tt}'+'} '
          el=Element(tb_dim_li[j],tb_elli[j],tb_coeli[j])
          if j==2 and '+' in tb_symli:
            symli=self.symbollist_to_tb_symbollist()[2]
            res+=el.el_sum(symli)[0][0]
          else: res+=el.tex()
      elif self.symbollist.count(',')==3:
        for j in range(6):
          if j==1: res+=' \{ '
          elif j==2 or j==3 or j==4: res+=', '
          elif j==5:
            if tt==0: res+=' \} '
            else: res+=' \}_{'+f'{tt}'+'} '
          el=Element(tb_dim_li[j],tb_elli[j],tb_coeli[j])
          res+=el.tex()
      return res

    def well_defined(self):
      tb_elli=self.ellist_to_tb_ellist()
      tb_coeli=self.coelist_to_tb_coelist()
      tb_symli=self.symbollist_to_tb_symbollist()
      tb_dim_li=self.tb_dim_list()
      el_cnt_li=self.tb_el_cnt_list()
      coe_li0=self.coelist

      tb_elli1=tb_elli[1]+tb_elli[2]
      tb_elli2=tb_elli[2]+tb_elli[3]
      tb_coeli1=tb_coeli[1]+tb_coeli[2]
      tb_coeli2=tb_coeli[2]+tb_coeli[3]
      el1=Element(tb_dim_li[1],tb_elli1,tb_coeli1)
      el2=Element(tb_dim_li[2]-tt,tb_elli2,tb_coeli2)
      if '+' in self.symbollist:
        el0=Element(tb_dim_li[1],tb_elli[1],tb_coeli[1])
        el1_0=Element(tb_dim_li[2],tb_elli[2],tb_coeli[2])
        el1_1=Element(tb_dim_li[2]-tt,tb_elli[2],tb_coeli[2])
        el2 = Element(tb_dim_li[3]-tt,tb_elli[3],tb_coeli[3])
        wd1=el0.tex()+'('+el1_0.el_sum(tb_symli[2])[0][0]+')'
        wd2='('+el1_1.el_sum(tb_symli[2])[0][0]+')'+el2.tex()
      else:
        wd1=el1.tex()
        wd2=el2.tex()
      el1=Element(tb_dim_li[1],tb_elli1,tb_coeli1)
      el2=Element(tb_dim_li[2]-tt+1,tb_elli2,tb_coeli2)

      len_coeli0=len(coe_li0)

      wd1_coeli0=[coe_li0[i] for i in range(len_coeli0) if el_cnt_li[0]<=i and i<el_cnt_li[0]+el_cnt_li[1]+el_cnt_li[2]]
      def_rel1=el1.deformation_relation(wd1_coeli0)
      rel_tex_li1,ref_tex_li1=el1.el_sum(tb_symli[0])
      wd1_rel=rel_tex_li1[-1]
      wd1_ref=' , '.join(ref_tex_li1)
      
      wd2_coeli0=[coe_li0[i] for i in range(len_coeli0) if el_cnt_li[0]+el_cnt_li[1]<=i and i<el_cnt_li[0]+el_cnt_li[1]+el_cnt_li[2]+el_cnt_li[3]]
      def_rel2=el2.deformation_relation(wd2_coeli0)
      
      rel_tex_li2,ref_tex_li2=el2.el_sum(tb_symli[1])
      wd2_rel=rel_tex_li2[-1]
      wd2_ref=' , '.join(ref_tex_li2)

      return wd1,wd2,wd1_rel,wd2_rel,wd1_ref,wd2_ref,def_rel1,def_rel2

    def coset(self):
      cos1=''
      cos2=''
      tb_elli=self.ellist_to_tb_ellist()
      tb_coeli=self.coelist_to_tb_coelist()
      tb_symli=self.symbollist_to_tb_symbollist()
      tb_dim_li=self.tb_dim_list()
      
      el1=Element(tb_dim_li[0],tb_elli[0]+tb_elli[1],tb_coeli[0]+tb_coeli[1])
      if self.symbollist.count(',')==2: el2=Element(tb_dim_li[5],tb_elli[4],tb_coeli[4])
      elif self.symbollist.count(',')==3: el2=Element(tb_dim_li[6],tb_elli[5],tb_coeli[5])

      if len(el1.ellist)==1 and el1.el_coelist!=[1]: cos1=f'({el1.tex()})'
      else: cos1=el1.tex()

      if self.symbollist.count(',')==2:
        if self.tt==0:
          cos1+=f' \pi_{ {tb_dim_li[5]} }^{ {tb_dim_li[2]} } '
          hg1=HomotopyGroup(tb_dim_li[2],tb_dim_li[5]-tb_dim_li[2])
        elif self.tt==1:
          cos1+=f' E \pi_{ {tb_dim_li[5]-1} }^{ {tb_dim_li[2]-1} } '
          hg1=HomotopyGroup(tb_dim_li[2]-1,tb_dim_li[5]-tb_dim_li[2])
        else:
          cos1+=f' E ^{ {self.tt} }\pi_{ {tb_dim_li[5]-self.tt} }^{ {tb_dim_li[2]-self.tt} } '
          hg1=HomotopyGroup(tb_dim_li[2]-self.tt,tb_dim_li[5]-tb_dim_li[2])
      elif self.symbollist.count(',')==3:
        if self.tt==0:
          cos1+=f' \pi_{ {tb_dim_li[5]+1} }^{ {tb_dim_li[2]} } '
          hg1=HomotopyGroup(tb_dim_li[2],tb_dim_li[5]-tb_dim_li[2]+1)
        elif self.tt==1:
          cos1+=f' E \pi_{ {tb_dim_li[5]} }^{ {tb_dim_li[2]-1} } '
          hg1=HomotopyGroup(tb_dim_li[2]-1,tb_dim_li[5]-tb_dim_li[2]+1)
        else:
          cos1+=f' E ^{ {self.tt} }\pi_{ {tb_dim_li[5]-self.tt+1} }^{ {tb_dim_li[2]-self.tt} } '
          hg1=HomotopyGroup(tb_dim_li[2]-self.tt, tb_dim_li[5]-tb_dim_li[2]+1)
      
      if len(el2.ellist)==1 and el2.el_coelist!=[1]: cos1+=f'({el2.tex()})'
      else: cos1+=el2.tex()
      cos_pi1=hg1.pi_tex()
      cos_pi_tex1=hg1.group_structure()

      cos_gen_li1=[]
      cos_pi_gen_li1=[]
      dsum1=hg1.direct_sum()
      for id in range(dsum1):
        hg1_rep_li=hg1.rep_list(id)
        cos_pi_gen_li1.append(hg1.el_tex(hg1_rep_li))
        
        if self.symbollist.count(',')==2:
          cos_elli1=tb_elli[0]+tb_elli[1]+hg1_rep_li+tb_elli[4]
          cos_coeli1=tb_coeli[0]+tb_coeli[1]+[1]*len(hg1_rep_li)+tb_coeli[4]
        elif self.symbollist.count(',')==3:
          cos_elli1=tb_elli[0]+tb_elli[1]+hg1_rep_li+tb_elli[5]
          cos_coeli1=tb_coeli[0]+tb_coeli[1]+[1]*len(hg1_rep_li)+tb_coeli[5]

        cos_el1=Element(self.n,cos_elli1,cos_coeli1)
        cos_el1_def_rel=cos_el1.deformation_relation(cos_coeli1)
        if cos_el1_def_rel[0]!=[]: cos_gen1=cos_el1_def_rel[0][-1]
        else: cos_gen1=cos_el1.tex()
        cos_gen_li1.append(cos_gen1)

      cos_gen_tex_li1=[' \{ '+gen+' \}' for gen in cos_gen_li1]
      coset_tex1=' + '.join(cos_gen_tex_li1)

      el3=Element(tb_dim_li[0],tb_elli[0],tb_coeli[0])
      if self.symbollist.count(',')==2: el4=Element(tb_dim_li[3]+1,tb_elli[3]+tb_elli[4],tb_coeli[3]+tb_coeli[4])
      elif self.symbollist.count(',')==3: el4=Element(tb_dim_li[4]+2,tb_elli[4]+tb_elli[5],tb_coeli[4]+tb_coeli[5])

      if len(el3.ellist)==1 and el3.el_coelist!=[1]: cos2=f'({el3.tex()})'
      else: cos2=el3.tex()

      if self.symbollist.count(',')==2: cos2+=f' \pi_{ {tb_dim_li[3]+1} }^{ {tb_dim_li[1]} } ' 
      elif self.symbollist.count(',')==3: cos2+=f' \pi_{ {tb_dim_li[3]+2} }^{ {tb_dim_li[1]} } ' 
      
      if len(el4.ellist)==1 and el4.el_coelist[0]!=1: cos2+=f'({el4.tex()})'
      else: cos2+=el4.tex()

      cos_gen_li2=[]
      if self.symbollist.count(',')==2: hg2=HomotopyGroup(tb_dim_li[1],tb_dim_li[3]-tb_dim_li[1]+1)
      elif self.symbollist.count(',')==3: hg2=HomotopyGroup(tb_dim_li[1],tb_dim_li[3]-tb_dim_li[1]+2)

      cos_pi2=hg2.pi_tex()
      cos_pi_tex2=hg2.group_structure()
      dsum2=hg2.direct_sum()
      for id in range(dsum2):
        hg2_rep_li=hg2.rep_list(id)

        if self.symbollist.count(',')==2:
          cos_elli2=tb_elli[0]+hg2_rep_li+tb_elli[3]+tb_elli[4]
          cos_coeli2=tb_coeli[0]+[1]*len(hg2_rep_li)+tb_coeli[3]+tb_coeli[4]
        elif self.symbollist.count(',')==3:
          cos_elli2=tb_elli[0]+hg2_rep_li+tb_elli[3]+tb_elli[4]+tb_elli[5]
          cos_coeli2=tb_coeli[0]+[1]*len(hg2_rep_li)+tb_coeli[3]+tb_coeli[4]+tb_coeli[5]
        
        cos_el2=Element(self.n,cos_elli2,cos_coeli2)
        cos_el2_def_rel=cos_el2.deformation_relation(cos_coeli2)
        if cos_el2_def_rel[0]!=[]: coset_gen2=cos_el2_def_rel[0][-1]
        else: coset_gen2=cos_el2.tex()
        cos_gen_li2.append(coset_gen2)

      cos_gen_tex_li2=[' \{ '+gen+' \} ' for gen in cos_gen_li2]
      coset_tex2=' + '.join(cos_gen_tex_li2)

      return cos1,cos2,coset_tex1,coset_tex2,cos_pi1,cos_pi2,cos_pi_tex1,cos_pi_tex2

#################################################

  total_coe0=1

  coe_list0=[int(request.form[f'coe_list[{i}]']) for i in range(6)]

  displays=[request.form[f'displays[{i}]'] for i in range(6)]

  el_list0=[el_id(display) for display in displays if display!=' ']

  symbols0=[request.form[f'symbols0[{i}]'] for i in range(7)]

  first_dim=request.form['first_dim']

  relation_tex_list=[]
  reference_tex_list=[]
  return_coe_list=[]

  el0=Element(n,el_list0,coe_list0,total_coe0)
  n=el0.change_first_dim(first_dim)
  el0=Element(n,el_list0,coe_list0,total_coe0)

  if '{' in symbols0:
    el_list0_0=el_list0
    coe_list0_0=coe_list0
  else:
    split_el_lili,split_coe_lili=el0.el_split(symbols0)
    el_list0_0=split_el_lili[0]
    coe_list0_0=split_coe_lili[0]

  k=k_dim(el_list0_0)

  if '{' in symbols0:
    tb=TodaBracket(n,tt,symbols0,el_list0,coe_list0)
    tb_dim_list0=tb.tb_dim_list()
    k=tb_dim_list0[-1]-tb_dim_list0[0]
  elif '[' in symbols0:
    wp=WhiteheadProduct(n,symbols0,el_list0,coe_list0)
    wp_ellist=wp.ellist_to_wp_ellist()
    wp_coelist=wp.coelist_to_wp_coelist()
    wp_dimlist=wp.wp_dim_list()
    wp_k=wp.wp_k()
    wp_change_ellist=wp.wp_ellist_to_ellist()

  display_mode=request.form['display_mode']

  if display_mode=='stable': n=k+2

  hg0=HomotopyGroup(n,k)
  el0_0=Element(n,el_list0_0,coe_list0_0,total_coe0)
  hg=HomotopyGroup(n,k)

  el_list1_0,coe_list1_0=hg.delete_iota(el_list0_0,coe_list0_0)

  if '{' in symbols0:
    tb=TodaBracket(n,tt,symbols0,el_list0,coe_list0)
    disp0=tb.tex()
  elif '[' in symbols0:
    wp=WhiteheadProduct(n,symbols0,el_list0,coe_list0)
    disp0=wp.tex()
  elif '+' in symbols0:
    if '(' in symbols0:
      disp0=''
      dis_split_el1_li=[]
      hg=HomotopyGroup(n,k)

      dis_tex1='+'.join(dis_split_el1_li)

      dis_li=[]
      relation_tex_list.append('+'.join(dis_li))
      reference_tex_list.append('')
    else:
      disp0_list=[]
      disp0='+'.join(disp0_list)
  else: disp0=el0_0.tex()

# case with Hopf map
  for i,elem in enumerate(el_list1_0):
    if elem in {2,4,9} and i>=1 and hg.el_sus_list(el_list1_0)[i]==0:
      if el_list1_0[i-1]==1:
        coe_list1_0[i]=coe_list1_0[i]*coe_list1_0[i-1]**2
        coe_list1_0[i-1]=1

  el_list2_0=el_list1_0
  coe_list2_0=coe_list1_0
  el_list1_0,coe_list1_0,total_coe1=hg.el_coe_out(el_list2_0, coe_list2_0)

  if '[' in symbols0:
    wp_el0=Element(n,wp_ellist[0],wp_coelist[0])
    p_ellist=wp_ellist[1]+wp_ellist[2]+wp_ellist[3]
    p_coelist=wp_coelist[1]+wp_coelist[2]+wp_coelist[3]
    wp_el1=Element(wp_dimlist[1]*2+1,p_ellist,p_coelist)
    relation_tex_list.append(f'{wp_el0.tex()} \Delta({wp_el1.tex()})')
    reference_tex_list.append('')

    if wp_change_ellist[0]!=[]:
      el_wp=Element(n,wp_change_ellist[0],wp_change_ellist[1])
      relation_tex_list.append(el_wp.tex())
      reference_tex_list.append('Prop 2.5, \ \Delta( E ^2 \gamma)=\pm[\iota_m, \iota_m]\gamma')
      deform_relation_tex_list,deform_reference_tex_list,deform_return_coe_list=el_wp.deformation_relation(wp_change_ellist[1])
      relation_tex_list.extend(deform_relation_tex_list)
      reference_tex_list.extend(deform_reference_tex_list)

# Prop2.2が適用できる場合
  if display_mode=='H-image' and len(el_list1_0)>=2:
    el1_0=Element(n,el_list1_0,coe_list1_0)
    if el1_0.sus_list()[0]>0:
      disp0=f'H({disp0})'
      el_list1_0_0=el_list1_0[:1]*2
      coe_list1_0_0=coe_list1_0[:1]*2
      el_list1_0_1=el_list1_0[1:]
      coe_list1_0_1=coe_list1_0[1:]
      el1_0_0=Element(2*n-1,el_list1_0_0,coe_list1_0_0)
      n1_0_1=el1_0.dim_list()[1]
      k1_0_1=el1_0.dim_list()[-1]-el1_0.dim_list()[1]
      el1_0_1=Element(n1_0_1,el_list1_0_1,coe_list1_0_1)
      relation_tex_list.append(el1_0_0.tex()+f'H({el1_0_1.tex()})')
      reference_tex_list.append('Prop 2.2, \ H(E\gamma\circ\\alpha)=E(\gamma\wedge\gamma)\circ H(\\alpha)')
      hg1_0_1=HomotopyGroup(n1_0_1,k1_0_1)
      ell1_0_1=ElementLinear(2*n1_0_1-1,n1_0_1-k1_0_1+1,hg1_0_1.H_coe(el1_0_1.element_to_id()[1])[0])
      add1_0_1=ell1_0_1.linear_to_el_list()
      if len(add1_0_1[0])==1:
        el_list1_0_0+=add1_0_1[0]
        coe_list1_0_0+=add1_0_1[1]
        el0=Element(2*n-1,el_list1_0_0,coe_list1_0_0)
        relation_tex_list.append(el0.tex())
        reference_tex_list.append(hg1_0_1.H_coe(el1_0_1.element_to_id()[1])[1])
        display_mode='tmp'
###############################

  hgP=HomotopyGroup((n-1)//2,n+k-2-(n-1)//2)
  hgE=HomotopyGroup(n+1,k)
  hgH=HomotopyGroup(2*n-1,k-n+1)

  if display_mode=='P-image':
    disp0=f'\Delta({disp0})'
    el1_0=Element(n,el_list1_0,coe_list1_0)
    if el1_0.element_to_id()[0]:
      relation_tex_list.append(hgP.rep_linear_tex(hg.P_coe(el1_0.element_to_id()[1])[0],total_coe1))
      reference_tex_list.append(hg.P_coe(el1_0.element_to_id()[1])[1])
    else:
      relation_tex_list.append('')
      reference_tex_list.append('')
  elif display_mode=='E-image':
    disp0=f'E({disp0})'
    el1_0=Element(n+1, el_list1_0,coe_list1_0)
    if el1_0.element_to_id()[0]:
      if hgE.rep_linear_tex(hg.E_coe(el1_0.element_to_id()[1])[0]) not in relation_tex_list \
      or hg.E_coe(el1_0.element_to_id()[1])[1] not in relation_tex_list:
        relation_tex_list.append(hgE.rep_linear_tex(hg.E_coe(el1_0.element_to_id()[1])[0], total_coe1))
        reference_tex_list.append(hg.E_coe(el1_0.element_to_id()[1])[1])
    else:
      for relation,reference in zip(el1_0.sus_element()[0],el1_0.sus_element()[1]):
        if relation not in relation_tex_list or reference not in reference_tex_list:
          relation_tex_list.append(relation)
          reference_tex_list.append(reference)
  elif display_mode=='H-image':
    disp0=f'H({disp0})'
    el1_0=Element(n,el_list1_0,coe_list1_0)
    if el1_0.element_to_id()[0]:
      relation_tex_list.append(hgH.rep_linear_tex(hg.H_coe(el1_0.element_to_id()[1])[0],total_coe1))
      reference_tex_list.append(hg.H_coe(el1_0.element_to_id()[1])[1])
    elif len(el_list1_0)>=2 and el1_0.sus_list()[0]>0:
      el_list1_0_0=el_list1_0[:1]*2
      coe_list1_0_0=coe_list1_0[:1]*2
      el_list1_0_1=el_list1_0[1:]
      coe_list1_0_1=coe_list1_0[1:]
      el1_0_0=Element(2*n-1,el_list1_0_0,coe_list1_0_0)
      el1_0_1=Element(el1_0.dim_list()[1],el_list1_0_1,coe_list1_0_1)
      relation_tex_list.append(el1_0_0.tex()+f'H({ el1_0_1.tex() })')
      reference_tex_list.append('Prop 2.2, \ H(E\gamma\circ\\alpha)=E(\gamma\wedge\gamma)\circ H(\\alpha)')
    else:
      relation_tex_list.append('')
      reference_tex_list.append('')
  elif '{' not in symbols0 and '[' not in symbols0 and display_mode!='Group-registration':
    if '+' in symbols0:
      relation_tex_list1,reference_tex_list1=el0.el_sum(symbols0)
      relation_tex_list.extend(relation_tex_list1)
      reference_tex_list.extend(reference_tex_list1)
    else:
      relation_tex_list,reference_tex_list,return_coe_list=el0.deformation_relation(coe_list0)
      if return_coe_list==[]:
        el0_subcomp0=el0.sub_comp(0,2)
        el0_0=Element(n,el0_subcomp0[0],el0_subcomp0[1])
        hg0_0=HomotopyGroup(n,el0_0.k)
        el0_0_has_relation=el0_0.has_relation()
        try:
          hg0_0_rep_coe_to_el_list=hg0_0.rep_coe_to_el_list(el0_0_has_relation[1])
          el0_0_list=[]
          for el in hg0_0_rep_coe_to_el_list[0]:
            for i in range(2,len(el0.ellist)):
              el.append(el0.ellist[i])
            el0_0_list.append(el)
          np_array=[]
          for el0_0_list_el in el0_0_list:
            el0_1=Element(n,el0_0_list_el)
            el0_1_deformation_relation=el0_1.deformation_relation()
            np_array.append(np.array(el0_1_deformation_relation[2]))
          pass
          
          sum_coe=sum(np_array)
          relation_tex_list.append(hg.rep_linear_tex(sum_coe))
        except:pass

  if display_mode=='tmp':
    display_mode='H-image'

  well_def1=''
  well_def2=''
  well_def1_relation=''
  well_def2_relation=''
  well_def1_reference=''
  well_def2_reference=''
  well_def1_deformation=''
  well_def2_deformation=''
  coset1=''
  coset2=''
  coset_tex1=''
  coset_tex2=''
  coset_pi1=''
  coset_pi2=''
  coset_pi_tex1=''
  coset_pi_tex2=''
  include_element_tex=''

  if '{' in symbols0:
    coset1,coset2,coset_tex1,coset_tex2,coset_pi1,coset_pi2,coset_pi_tex1,coset_pi_tex2=tb.coset()
    well_def1,well_def2,well_def1_relation,well_def2_relation,well_def1_reference,well_def2_reference,\
      well_def1_deformation,well_def2_deformation=tb.well_defined()

    if well_def1_relation=='0' and well_def2_relation=='0':
      include_element_list=tb.include_element_list()
      include_el=Element(n,include_element_list[0])
      if reference_tex_list==[]: reference_tex_list.append(include_element_list[1])
      else: reference_tex_list[0]=include_element_list[1]
      include_element_tex=include_el.tex()
      include_id=include_el.element_to_id()

  if display_mode=='stable': group_tex=hg.stable_group_structure()
  elif display_mode!='Group-registration': group_tex=hg.group_structure()
  else:group_tex=''

  group1_tex=''
  group1=[]

  if display_mode=='P-image':
    if n+k-2-(n-1)//2<=-1: query=f'select*from sphere where n={0} and k={-1}'
    elif n+k-2-(n-1)//2+2>=(n-1)//2: query=f'select*from sphere where n={(n-1)//2} and k={n+k-2-(n-1)//2}'
    else: query=f'select*from sphere where n={n+k-2-(n-1)//2+2} and k={n+k-2-(n-1)//2}'
    for row in c.execute(query):
      if row['orders']==0: group1.append('0')
      elif row['orders']==inf: group1.append('Z')
      else: group1.append(f"Z_{ {int(row['orders'])} }")
    group1_gen=[hgP.rep_linear_tex(hgP.gen_coe_list(j)) for j in range(hgP.direct_sum())]
    group1_tex_list=[gr+'\{'+gen+'\}' for (gr,gen) in zip(group1,group1_gen)]
    group1_tex=' \oplus '.join(group1_tex_list)
    if well_def1_relation=='0' and well_def2_relation=='0':
      if include_id[0]:
        hg_P_image_tex=hg.P_image_tex(include_id[1])
        include_element_tex=f'\Delta({include_element_tex})\ = '+hg_P_image_tex[0]
        if hg_P_image_tex[1]!=None: reference_tex_list[0]=reference_tex_list[0]+' \ , \ '+hg_P_image_tex[1]
  elif display_mode=='E-image':
    if k<=-1: query=f'select*from sphere where n={0} and k={-1}'
    elif k+2>=n+1: query=f'select*from sphere where n={n+1} and k={k}'
    else: query=f'select*from sphere where n={k+2} and k={k}'
    for row in c.execute(query):
      if row['orders']==0: group1.append('0')
      elif row['orders']==inf: group1.append('Z')
      else: group1.append(f"Z_{ {int(row['orders'])} }")
    group1_gen=[hgE.rep_linear_tex(hgE.gen_coe_list(j)) for j in range(hgE.direct_sum())]
    group1_tex_list=[gr+'\{'+gen+'\}' for (gr,gen) in zip(group1,group1_gen)]
    group1_tex=' \oplus '.join(group1_tex_list)
    if well_def1_relation=='0' and well_def2_relation=='0':
      if include_id[0]:
        hg_E_image_tex=hg.E_image_tex(include_id[1])
        include_element_tex=f' E ({include_element_tex})\ = '+hg_E_image_tex[0]
        if hg_E_image_tex[1]!=None: reference_tex_list[0]=reference_tex_list[0]+' \ , \ '+hg_E_image_tex[1]
  elif display_mode=='H-image':
    if k-n+1<=-1: query=f'select*from sphere where n={0} and k={-1}'
    elif k-n+3>=2*n-1: query=f'select*from sphere where n={2*n-1} and k={k-n+1}'
    else: query=f'select*from sphere where n={k-n+3} and k={k-n+1}'
    for row in c.execute(query):
      if row['orders']==0: group1.append('0')
      elif row['orders']==inf: group1.append('Z')
      else:group1.append(f"Z_{ {int(row['orders'])} }")
    group1_gen=[hgH.rep_linear_tex(hgH.gen_coe_list(j)) for j in range(hgH.direct_sum())]
    group1_tex_list=[gr+'\{'+gen+'\}' for (gr,gen) in zip(group1,group1_gen)]
    group1_tex=' \oplus '.join(group1_tex_list)
    if well_def1_relation=='0' and well_def2_relation=='0':
      if include_id[0]:
        hg_H_image_tex=hg.H_image_tex(include_id[1])
        include_element_tex=f'H({include_element_tex})\ = '+hg_H_image_tex[0]
        if hg_H_image_tex[1]!=None: reference_tex_list[0]=reference_tex_list[0]+' \ , \ '+hg_H_image_tex[1]
  relation_count=len(relation_tex_list)

  conn.close()

  return render_template('relation.html', n=n, k=k, tt=tt \
    , display_list=display_list \
    , disp0=disp0, displays=displays, coe_list0=coe_list0 \
    , stable_displays=stable_displays, stable_symbols0=stable_symbols0 \
    , stable_display_list=stable_display_list, stable_symbol_list=stable_symbol_list \
    , relation_tex_list=relation_tex_list, group_tex=group_tex \
    , reference_tex_list=reference_tex_list, relation_count=relation_count \
    , first_dim=first_dim, coe_list=coe_list \
    , group1=group1, group1_tex=group1_tex, display_mode=display_mode \
    , return_coe_list=return_coe_list, symbol_list=symbol_list, symbols0=symbols0 \
    , well_def1=well_def1, well_def2=well_def2 \
    , well_def1_relation=well_def1_relation, well_def2_relation=well_def2_relation \
    , well_def1_reference=well_def1_reference, well_def2_reference=well_def2_reference \
    , coset1=coset1, coset2=coset2, coset_tex1=coset_tex1, coset_tex2=coset_tex2 \
    , coset_pi1=coset_pi1, coset_pi_tex1=coset_pi_tex1 \
    , coset_pi2=coset_pi2, coset_pi_tex2=coset_pi_tex2 \
    , well_def1_deformation=well_def1_deformation, well_def2_deformation=well_def2_deformation \
    , include_element_tex=include_element_tex \
    )


if __name__ == "__main__":
  app.run(debug=True)

