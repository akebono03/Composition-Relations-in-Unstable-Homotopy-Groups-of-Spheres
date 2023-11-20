from re import template
from weakref import ReferenceType
from flask import Flask, render_template, request #追加
from jinja2 import Template
import sqlite3
import numpy as np
import pandas as pd
import sympy as sp
import os

app = Flask(__name__)

df = pd.read_csv('./HyoujiGen.csv')
display_list = df['display'].unique().tolist()
symbol_list = [' ', ',', '{', '}', '[', ']', '+']

n = 2
k = 0
tt = 0
coe_list = [1]*6
coe_list0 = [1]*6
displays = ['','','','','','']
relation_tex_list = []
reference_tex_list = []
relation_count = 0
display_mode = ''
symbols0 = ['', '', '', '', '', '', '']

@app.route('/')
def relation():
  return render_template('relation.html', display_list=display_list, coe_list0=coe_list0 \
    , n=n, k=k, tt=tt, coe_list=coe_list, displays=displays, display_mode=display_mode\
    , relation_tex_list=relation_tex_list, reference_tex_list=reference_tex_list \
    , relation_count=relation_count, symbol_list=symbol_list, symbols0=symbols0) #変更

@app.route('/register', methods=['post'])
def register():
  n = request.form['n']
  n = int(n)

  tt = request.form['tt']
  tt = int(tt)

  db_name = 'sphere.db'
  conn = sqlite3.connect(db_name)
  df = pd.read_csv('./sphere.csv')
  df.to_sql('sphere', conn, if_exists='replace')
  df = pd.read_csv('./HyoujiGen.csv')
  df.to_sql('gen', conn, if_exists='replace')
  df = pd.read_csv('./TBtable.csv')
  df.to_sql('TBtable', conn, if_exists='replace')
  df = pd.read_csv('./sphere_relation2.csv')
  df.to_sql('sphere_relation', conn, if_exists='replace')
  c = conn.cursor()

  inf = float('inf')

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
                if sq_cnt>=2:res= res.removesuffix('}')+f'^{ {sq_cnt} }'+'}'
            elif el_li[i]!= el_li[i+1]:
#次のidと違うときにtexを追加
              if el_dim_li[i] >=row['n']:
                if '{3,' in row['latex'] or '{4,' in row['latex']:res+='{' +row['latex'] +f'{el_dim_li[i-sq_cnt+1]}'+'} }'
                else:res+='{'+ row['latex']+f'_{ {el_dim_li[i-sq_cnt+1]} }'+'}'
                if sq_cnt>=2:res= res.removesuffix('}')+f'^{ {sq_cnt} }'+'}'
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
              if res[-1]==')':res=res.removesuffix('})')+f'^{ {sq_cnt} }'+'})'
              else:res=res.removesuffix('}')+f'^{ {sq_cnt} }'+'}'
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
              if res[-1]==')':res=res.removesuffix('})')+f'^{ {sq_cnt} }'+'})'
              else:res=res.removesuffix('}')+f'^{ {sq_cnt} }'+'}'
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
            elif rep_coe[i]%ord_li[i]>ord_li[i]/2: return rep_coe[i]%ord_li[i]-ord_li[i]
            else: return rep_coe[i]%ord_li[i]
          except: return rep_coe[i]
        A=sp.Matrix([mod_coe(i) for i in range(direct_sum)])
        res=str(Dot(X,A)).replace('*x','x')
        for i in range(direct_sum):
          res=res.replace(symbol_li[i],self.el_tex(self.rep_list(i)))
      else:res=''
      return res



    def P_coe(self, id):
      int_list = []
      ref_tex = ''
      order_list = self.order_list()
      try:
        if order_list == [0] or order_list == []:
          int_list = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        else:
          queryid = f'select * from sphere where n = {self.n} and k = {self.k} and id = {id}'
          for row in c.execute(queryid):
            if row['P_coe'] is not None:
              int_list = list(map(int, row['P_coe'].split()))
              ref_tex = row['P']  
      except:
        pass
      del int_list[HomotopyGroup((self.n - 1) / 2, (self.n + 2 * self.k - 3) / 2).direct_sum():] 
      # リストの長さを direct_sum の個数にする
      return int_list, ref_tex

    def E_coe(self, id):
      int_list = []
      ref = []
      for row in c.execute(self.query_id(id)):
        if row['E_coe'] is not None:
          int_list = list(map(int, row['E_coe'].split()))
          ref = row['E'] #if row['E'] is not None else '' 
        hg = HomotopyGroup(self.n+1, self.k) if self.k+2 >= self.n \
          else HomotopyGroup(self.k+2, self.k)
        del int_list[hg.direct_sum():]
      return int_list, ref

    def H_coe(self, id):
      int_list = []
      ref_tex = ''
      if self.k + 2 >= self.n:
        for row in c.execute(self.query_id(id)):
          if row['H_coe'] is not None:
            int_list = list(map(int, row['H_coe'].split()))
            ref_tex = row['H']
      else:
        int_list = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      del int_list[HomotopyGroup(2 * self.n - 1, self.k - self.n + 1).direct_sum():] 
      # リストの長さを direct_sum の個数にする
      return int_list, ref_tex

    def P_image_tex(self, id):
      if self.n % 2 == 1:
        P_hg = HomotopyGroup(int((self.n - 1) / 2), int((self.n + 2 * self.k - 3) / 2))
        return_P_image_tex = P_hg.rep_linear_tex(self.P_coe(id)[0])
      else:
        return_P_image_tex = ''
      return return_P_image_tex

    def E_image_tex(self, id):
      E_hg = HomotopyGroup(self.n+1, self.k)
      return_E_image_tex = E_hg.rep_linear_tex(self.E_coe(id)[0])
      return return_E_image_tex

    def H_image_tex(self, id):
      H_hg = HomotopyGroup(2*self.n-1,self.k-self.n+1)
      return_H_image_tex = H_hg.rep_linear_tex(self.H_coe(id)[0])
      return return_H_image_tex

    def rep_coe_to_id_list(self, repcoelist):
      return_id_list = [i for i in range(self.direct_sum()) if repcoelist[i] != 0]
      return_coe_list = [repcoelist[i] for i in return_id_list]
      return return_id_list, return_coe_list

    def rep_coe_to_el_list(self, repcoelist):
      id_list = self.rep_coe_to_id_list(repcoelist)
      return_el_list = [self.rep_list(i) for i in id_list[0]]
      return_coe_list = id_list[1]
      return return_el_list, return_coe_list

    def P_coe_matrix(self):
      matrix_list = []
      direct_sum = self.direct_sum()
      for id in range(direct_sum):
        for row in c.execute(self.query_id(id)):
          int_list = list(map(int, row['P_coe'].split()))
        del int_list[direct_sum:]
        matrix_list.append(int_list)
      return_P_coe_matrix = sp.Matrix(matrix_list)
      return return_P_coe_matrix

    def E_coe_matrix(self):
      matrix_list = []
      direct_sum = self.direct_sum()
      for id in range(direct_sum):
        for row in c.execute(self.query_id(id)):
          int_list = list(map(int, row['E_coe'].split()))
        del int_list[direct_sum:]
        matrix_list.append(int_list)
      return_E_coe_matrix = sp.Matrix(matrix_list)
      return return_E_coe_matrix

    def H_coe_matrix(self):
      matrix_list = []
      direct_sum = self.direct_sum()
      for id in range(direct_sum):
        for row in c.execute(self.query_id(id)):
          int_list = list(map(int, row['H_coe'].split()))
        del int_list[direct_sum:]
        matrix_list.append(int_list)
      return_H_coe_matrix = sp.Matrix(matrix_list)
      return return_H_coe_matrix

    def rep_to_gen_matrix(self):
      matrix_list = []
      direct_sum = self.direct_sum()
      for id in range(direct_sum):
        for row in c.execute(self.query_id(id)):
          int_list = list(map(int, row['gen_coe'].split()))
        del int_list[direct_sum:]
        matrix_list.append(int_list)
      return_matrix = sp.Matrix(matrix_list)
      return return_matrix

    def rep_coe_to_gen_coe(self, repcoelist):
      repcoematrix = sp.Matrix([repcoelist])
      return_gen_coe_list = (repcoematrix * self.rep_to_gen_matrix().inv()).tolist()[0]
      return return_gen_coe_list

    def gen_coe_to_rep_coe(self, gencoelist):
      gencoematrix = sp.Matrix([gencoelist])
      return_rep_coe_list = (gencoematrix * self.rep_to_gen_matrix()).tolist()[0]
      return return_rep_coe_list

    def mod_gen_coe_list(self, gencoe):
      order_list = self.order_list()
      direct_sum = self.direct_sum()
      def mod_coe(i):
        if order_list[i] == inf:
          return gencoe[i]
        elif gencoe[i] % order_list[i] > order_list[i] /2:
          return gencoe[i] % order_list[i] - order_list[i]
        else:
          return gencoe[i] % order_list[i]
      return_mod_gen_coe_list = [mod_coe(i) for i in range(direct_sum)]
      return return_mod_gen_coe_list

    def group_is_zero(self):
      groupiszero = False
      for row in c.execute(self.query):
        groupiszero = True if row['orders'] == 0 else False
      return groupiszero

    def sub_comp_tex_list(self, el_list, el_coe_list, t):
      sub_comp_list = self.sub_comp_list(el_list, el_coe_list, t)
      return_sub_comp_tex_list = []
      for i in range(len(sub_comp_list[0])):
        sub_n = sub_comp_list[0][i]
        sub_k = sub_comp_list[1][i]
        sub_el_list = sub_comp_list[2][i]
        sub_el_coe_lsit = sub_comp_list[3][i]
        sub_hg = HomotopyGroup(sub_n, sub_k)
        return_sub_comp_tex_list.append(sub_hg.el_coe_tex(sub_el_list, sub_el_coe_lsit))
      return return_sub_comp_tex_list


  class ElementLinear:
    def __init__(self, n, k, coe_list):
      self.n = n
      self.k = k
      self.coe_list = coe_list
    
    def direct_sum(self):
      hg = HomotopyGroup(self.n, self.k)
      return hg.direct_sum()

    def coe_cut(self):
      return self.coe_list[:self.direct_sum()]

    def E_coe(self):
      M = np.array([self.coe_cut()])
      hg = HomotopyGroup(self.n, self.k)
      direct_sum = hg.direct_sum()
      N = np.array([hg.E_coe(i)[0] for i in range(direct_sum)])
      try:
        if type((M @ N)[0]) == list:
          Ecoe = (M @ N)[0]
        else:
          Ecoe = (M @ N)[0].tolist()
        ref_list = [hg.E_coe(i)[1] for i in range(direct_sum) 
          if self.coe_list[i] != 0 and hg.E_coe(i)[1] is not None]
      except ValueError:
        Ecoe = []
        ref_list = []
      if Ecoe == 0:
        Ecoe = [0]
      return Ecoe, ref_list

    def rep_linear_order(self):
      direct_sum = self.direct_sum()
      replinorder = 0
      hg = HomotopyGroup(self.n, self.k)
      order_list = hg.order_list()
      if inf in order_list:
        replinorder = inf
      else:
        replinorder = max([cyclic_order(self.coe_list[i], int(order_list[i])) 
          for i in range(direct_sum)])
      return replinorder

    def linear_to_el_list(self):
      return_el_list = []
      return_coe_list = []
      if np.count_nonzero(self.coe_list) == 1:
        for j in range(len(self.coe_list)):
          if self.coe_list[j] != 0:
            hg = HomotopyGroup(self.n, self.k)
            return_el_list = hg.rep_list(j)
            return_coe_list = [1 if i != len(return_el_list)-1 
              else self.coe_list[j] for i in range(len(return_el_list))]
      return return_el_list, return_coe_list


  class Element: 
    def __init__(self, n, ellist=[1], el_coelist=[1]*6, total_coe=1):
      self.n = n
      self.ellist = ellist
      self.el_coelist = el_coelist
      self.total_coe = total_coe

      self.k = k_dim(ellist)

    def tex(self):
      hg = HomotopyGroup(self.n, self.k)
      el_coe_tex = hg.el_coe_tex(self.ellist, self.el_coelist)
      if self.total_coe == 1:
        eltex = el_coe_tex
      elif len(self.ellist) == 1:
        eltex = str(self.total_coe) + el_coe_tex
      else:
        eltex = str(self.total_coe) + '(' + el_coe_tex + ')'
      return eltex

    def dim_list(self):
      hg = HomotopyGroup(self.n, self.k)
      return hg.el_dim_list(self.ellist)

    def sus_list(self):
      dim_list = self.dim_list()
      suslist = []
      for (i, elem) in enumerate(self.ellist):
        gen_query = f'select * from gen where id = "{elem}" '
        for row in c.execute(gen_query):
          suslist.append(dim_list[i] - row['n'])
      return suslist

    def desus_max(self):
      sus_list = self.sus_list()
      if sus_list != []:
        return_desus_max = min(sus_list)
      else:
        return_desus_max = 0
      return return_desus_max

    def delete_iota(self):
      delete_num = []
      for (i, elem) in enumerate(self.ellist):
        if elem == 1 and self.el_coelist[i] == 1:
          delete_num.append(i)
      return_ellist = [self.ellist[i] for i in range(len(self.ellist)) if i not in delete_num]
      try:
        return_el_coelist = [self.el_coelist[i] for i in range(len(self.ellist)) if i not in delete_num] 
      except IndexError:
        return_el_coelist = []
      return return_ellist, return_el_coelist


    def can_take_out_el_coe(self, i):
      sus_list = self.sus_list()
      dim_list = self.dim_list()
      cantakeout = False
      if dim_list[i+1] in {1,3,7}:
        cantakeout = True
      if sus_list[i+1:] != []:
        if min(sus_list[i+1:]) >= 1:
          cantakeout = True
      elif len(self.ellist) == i+1:
        cantakeout = True
      return cantakeout

    def el_coe_out(self):
      out_coe = self.total_coe
      for i in range(len(self.ellist)):
        if self.can_take_out_el_coe(i):
          try:
            out_coe = out_coe * self.el_coelist[i]
            self.el_coelist[i] = 1
          except IndexError:
            pass
      (after_el_list, after_el_coe_list) = self.delete_iota()
      return after_el_list, after_el_coe_list, out_coe

    def include_EP(self):
      includeEP = False
      for (i, elem) in enumerate(self.ellist):
        gen_query = f'select * from gen where id = "{elem}" '
        for row in c.execute(gen_query):
          if 'P(' in row['display'] and self.dim_list()[i] - row['n'] > 0:
            includeEP = True
      return includeEP

    def is_rep_element(self):
      isrepelement = False
      rep_id = None
      rep_coe_list = [0]*12
      del rep_coe_list[HomotopyGroup(self.n, self.k).direct_sum():]
      el_str = ' '.join(map(str, self.ellist))
      query_rep_count = f'select count( * ) from sphere where n = {self.n} and Element = "{el_str}"'
      for row in c.execute(query_rep_count):
        if row['count( * )'] >=1:
          isrepelement = True
          query_rep_id = f'select * from sphere where n = {self.n} and Element = "{el_str}" '
          for row in c.execute(query_rep_id):
            rep_id = int(row['id'])
            rep_coe_list[int(rep_id)] = 1
      return isrepelement, rep_id, rep_coe_list

    def sus_element(self, totalcoe=1):
      rel_tex_list = []
      ref_tex_list = []
      return_n = []
      return_k = []
      return_sus_rep_coe = []
      el_str = ' '.join(map(str, self.ellist))
      for i in range(self.desus_max()):
        query_rep_count = f'select count( * ) from sphere where n = {self.n-i-1} and Element = "{el_str}"'
        for row_count in c.execute(query_rep_count):
          if row_count['count( * )'] >=1:
            query_rep = f'select * from sphere where n = {self.n-i-1} and Element = "{el_str}"'
            for row in c.execute(query_rep):
              coe_list = [0] * 11
              coe_list.insert(int(row['id']), totalcoe)
              for j in range(i+1):
                hg = HomotopyGroup(self.n-i+j, self.k)
                el_lin = ElementLinear(self.n-i+j-1, self.k, coe_list)
                el_lin_E_coe = el_lin.E_coe()
                rep_linear_tex = hg.rep_linear_tex(el_lin_E_coe[0])
                non_zero_list = [i for i in el_lin_E_coe[0] if i != 0]
                if not (len(non_zero_list) == 1 and non_zero_list[0] == 1):
                  if i-j>=2:
                    if totalcoe == 1:
                      rel_tex_list.append(f'\Sigma^{ {i-j} } ({rep_linear_tex} )')
                    else:
                      rel_tex_list.append(f'{totalcoe} (\Sigma^{ {i-j} } ({rep_linear_tex} ))')
                  elif i-j==1:
                    if totalcoe == 1:
                      rel_tex_list.append(f'\Sigma ({rep_linear_tex} )')
                    else:
                      rel_tex_list.append(f'{totalcoe} (\Sigma ({rep_linear_tex} ))')
                  else:
                    rel_tex_list.append(hg.rep_linear_tex(el_lin_E_coe[0], totalcoe))
                  ref_tex_list.append(', '.join(el_lin_E_coe[1]))
                return_n = hg.n
                return_k = hg.k
                return_sus_rep_coe.append(el_lin_E_coe[0])
                coe_list = el_lin_E_coe[0]
            break
      return rel_tex_list, ref_tex_list, return_n, return_k, return_sus_rep_coe

    def has_relation(self):
      hg = HomotopyGroup(self.n, self.k)
      direct_sum = hg.direct_sum()
      hasrelation = (False, [], '')
      el_str = ' '.join(map(str, self.ellist))
      query_relation_count = f'select count( * ) from sphere_relation where n = {self.n} and el_str = "{el_str}"'
      for row_count in c.execute(query_relation_count):
        if row_count['count( * )'] >=1:
          query_relation = f'select * from sphere_relation where n = {self.n} and el_str = "{el_str}"'
          for row in c.execute(query_relation):
            relation_rep_coe = [list(map(int, row['rep_coe'].split()))[i] for i in range(direct_sum)]
            relation_ref = row['reference']
            hasrelation = (True, relation_rep_coe, relation_ref)
      return hasrelation

    def has_sus_relation(self, totalcoe=1):
      rel_tex_list = []
      ref_tex_list = []
      return_n = []
      return_k = []
      return_relation_rep_coe = []
      for i in range(self.desus_max()):
        el = Element(self.n-i-1, self.ellist, self.el_coelist)
        el_has_relation = el.has_relation()
        if el_has_relation[0]:
          coe_list = el_has_relation[1]
          return_n.append(el.n)
          return_k.append(el.k)
          return_relation_rep_coe.append(coe_list)
          hg = HomotopyGroup(self.n-i-1, self.k)
          rep_linear_tex_coe_list = hg.rep_linear_tex(coe_list)
          if i>=1:
            if totalcoe == 1:
              rel_tex_list.append(f'\Sigma^{ {i+1} } ({rep_linear_tex_coe_list} )')
            else:
              rel_tex_list.append(f'{totalcoe} (\Sigma^{ {i+1} } ({rep_linear_tex_coe_list} ))')
          elif i==0:
            if totalcoe == 1:
              rel_tex_list.append(f'\Sigma ({rep_linear_tex_coe_list} )')
            else:
              rel_tex_list.append(f'{totalcoe} (\Sigma ({rep_linear_tex_coe_list} ))')
          else:
            rel_tex_list.append(hg.rep_linear_tex(coe_list, totalcoe))
          ref_tex_list.append(el_has_relation[2])
          for j in range(i+1):
            hg = HomotopyGroup(self.n-i+j, self.k)
            el_lin = ElementLinear(self.n-i+j-1, self.k, coe_list)
            el_lin_E_coe = el_lin.E_coe()
            rep_linear_tex_el_lin_E_coe = hg.rep_linear_tex(el_lin_E_coe[0])
            if i-j>=2:
              if totalcoe == 1:
                rel_tex_list.append(f'\Sigma^{ {i-j} } ({rep_linear_tex_el_lin_E_coe} )')
              else:
                rel_tex_list.append(f'{totalcoe} (\Sigma^{ {i-j} } ({rep_linear_tex_el_lin_E_coe} ))')
            elif i-j==1:
              if totalcoe == 1:
                rel_tex_list.append(f'\Sigma ({rep_linear_tex_el_lin_E_coe} )')
              else:
                rel_tex_list.append(f'{totalcoe} (\Sigma ({rep_linear_tex_el_lin_E_coe} ))')
            else:
              rel_tex_list.append(hg.rep_linear_tex(el_lin_E_coe[0], totalcoe))
            ref_tex_list.append(', '.join(el_lin_E_coe[1]))
            coe_list = el_lin_E_coe[0]
            return_n.append(el_lin.n+1)
            return_k.append(el_lin.k)
            return_relation_rep_coe.append(coe_list)
          break
      return rel_tex_list, ref_tex_list, return_n, return_k, return_relation_rep_coe

    def composition_is_zero(self):
      has_sus_relation = self.has_sus_relation()
      return_composition_is_zero = False
      rel_tex = ''
      ref_tex = ''
      if '0' in has_sus_relation[0]:
        return_composition_is_zero = True
        rel_tex = has_sus_relation[0][0]
        ref_tex = has_sus_relation[1][0]
      return return_composition_is_zero, rel_tex, ref_tex

    def element_to_id(self):
      return_element_to_id = False
      element_id = None
      el_list_str = ' '.join(list(map(str, self.ellist)))
      query = f'select * from sphere where n = {self.n} and Element = "{el_list_str}" '
      for row in c.execute(query):
        element_id = int(row['id'])
        return_element_to_id = True
      return return_element_to_id, element_id

    def element_to_linear_coe(self):
      element_to_id = self.element_to_id()
      return_linear_coe = []
      if element_to_id[0]:
        return_linear_coe = [0]*12 
        return_linear_coe[element_to_id[1]] = 1
      return return_linear_coe

    def is_P_image(self):
      ellist0 = self.ellist
      elem = self.ellist[0]
      gen_query = f'select * from gen where id = "{elem}" '
      for row in c.execute(gen_query):
        if 'P(' in row['display']:
          return_is_P_image = True
          P_n = row['n'] # = self.n
          P_k = row['k'] # = self.dim_list()[1] - self.n
          el_P = Element(P_n, [elem])
          return_P_n = 2 * P_n + 1
          return_P_k = P_k - P_n + 1
          coe_str = ' '.join(list(map(str, el_P.element_to_linear_coe())))
          query = f'select * from sphere where n = {return_P_n} and k = {return_P_k} and P_coe = "{coe_str}" '
          return_el_list = ellist0
          for P_row in c.execute(query):
            try:
              return_el_list = [int(P_row['Element'])] + ellist0[1:]
            except ValueError:
              return_el_list = list(map(int, P_row['Element'].split())) + ellist0[1:]
          comp_el_P = Element(P_n, return_el_list)
          comp_el_P_dim_list = comp_el_P.dim_list()
          return_P_k = comp_el_P_dim_list[-1] - comp_el_P_dim_list[0]
        else:
          return_is_P_image = False
          return_el_list = ellist0
          return_P_n = 0
          return_P_k = 0
      return return_is_P_image, return_P_n, return_P_k, return_el_list

    def el_dim_list(self): # 表示元の境目の次元のリストを与えるメソッド
      el_d = [self.n]
      for (i, elem) in enumerate(self.ellist):
        gen_query = f'select * from gen where id = "{elem}" '
        for row in c.execute(gen_query):
          el_d.append(el_d[i] + row['k'])
      return el_d

    def sub_comp(self, i, j):
      sub_el_list = self.ellist[i:i+j]
      sub_el_coe_list = self.el_coelist[i:i+j]
      return sub_el_list, sub_el_coe_list 

    def total_coe_to_sub_comp(self, i, j):
      return_total_coe_to_sub_comp = False
      suslist = self.sus_list()[i+j+1:]
      suslist.append(self.dim_list()[-1])
      if min(suslist) >= 1:
        return_total_coe_to_sub_comp = True
      return return_total_coe_to_sub_comp

    def sub_comp_list(self, t):
      el_list = self.ellist
      el_coe_list = self.el_coelist
      el_dim_list = self.el_dim_list()
      subcomplist_n = []
      subcomplist_k = []
      subcomplist_el = []
      subcomplist_el_coe = []
      bin_t = bin(t)[2:]
      bin_t0 = '0'*(len(el_list)-1 - len(bin_t)) + bin_t + '1'
      j = 1
      for i in range(len(el_list)):
        if i == 0:
          subcomplist_n.append(el_dim_list[0])
        elif bin_t0[i-1] == '1':
          subcomplist_n.append(el_dim_list[i])
        if bin_t0[i] == '1':
          sub_comp = self.sub_comp(i-j+1, j)
          subcomplist_el.append(sub_comp[0])
          subcomplist_el_coe.append(sub_comp[1])
          j = 1
        else:
          j = j + 1
      for i in range(len(subcomplist_n)):
        if i <= len(subcomplist_n)-2:
          subcomplist_k.append(subcomplist_n[i+1]-subcomplist_n[i])
        else:
          subcomplist_k.append(el_dim_list[-1]-subcomplist_n[-1])
      return subcomplist_n, subcomplist_k, subcomplist_el, subcomplist_el_coe

    def sub_comp_tex_list(self, t):
      sub_comp_list = self.sub_comp_list(t)
      return_sub_comp_tex_list = []
      for i in range(len(sub_comp_list[0])):
        sub_n = sub_comp_list[0][i]
        sub_k = sub_comp_list[1][i]
        sub_el_list = sub_comp_list[2][i]
        sub_el_coe_lsit = sub_comp_list[3][i]
        sub_hg = HomotopyGroup(sub_n, sub_k)
        return_sub_comp_tex_list.append(sub_hg.el_coe_tex(sub_el_list, sub_el_coe_lsit))
      return return_sub_comp_tex_list

    def change_el_list(self, i, j, sub_ellist, sub_el_coelist):
      if sub_ellist != []:
        return_ellist = []
        return_el_coelist = []
        return_ellist.extend(self.ellist)
        return_ellist[i:i+j] = sub_ellist
        return_el_coelist.extend(self.el_coelist)
        return_el_coelist[i:i+j] = sub_el_coelist
      else:
        return_ellist = self.ellist
        return_el_coelist = self.el_coelist
      return return_ellist, return_el_coelist

    def change_el_list_list(self, i_list, j_list, sub_ellist_list, sub_el_coelist_list):
      return_ellist = [e for e in self.ellist]
      return_el_coelist = [c for c in self.el_coelist]
      for ii in reversed(range(len(return_ellist))):
        if ii in i_list:
          i = i_list.index(ii)
          jj = j_list[i]
          return_ellist[ii:ii+jj] = sub_ellist_list[i]
          return_el_coelist[ii:ii+jj] = sub_el_coelist_list[i]
      return return_ellist, return_el_coelist

    def include_zero_subcomp(self):
      return_include_zero = False
      return_rel_list = []
      return_ref_list = []
      for t in range(2**(len(self.ellist)-1)):
        (t_n_list, t_k_list, t_el_list, t_el_coe_list) = self.sub_comp_list(t)
        for i in range(len(t_n_list)):
          t_i_hg = HomotopyGroup(t_n_list[i], t_k_list[i])
          t_i_el = Element(t_n_list[i], t_el_list[i], t_el_coe_list[i])
          t_i_el_composition_is_zero = t_i_el.composition_is_zero()
          if t_i_hg.group_is_zero():
            return_include_zero = True
            return_rel_list.append('0')
            el_tex = t_i_el.tex()
            return_ref_list.append(f'{el_tex} \in \pi_{ {t_n_list[i] + t_k_list[i]} }^{ {t_n_list[i]} }=0')
          if t_i_el_composition_is_zero and t_i_el_composition_is_zero[1] != '':
            return_include_zero = True
            return_rel_list.append('0')
            return_ref_list.append(t_i_el_composition_is_zero[2])
      return return_include_zero, return_rel_list, return_ref_list

    def element_order(self):
      is_rep_element = self.is_rep_element()
      sus_element = self.sus_element()
      has_relation = self.has_relation()
      has_sus_relation = self.has_sus_relation()
      return_element_order = None
      rep_coe_list = []
      if is_rep_element[0]:
        rep_coe_list = is_rep_element[2]
      elif sus_element[4] != []:
        rep_coe_list = sus_element[4][-1]
      elif has_relation[0]:
        rep_coe_list = has_relation[1]
      elif has_sus_relation[4] != []:
        rep_coe_list = has_sus_relation[4][-1]
      if rep_coe_list != []:
        el_lin = ElementLinear(self.n, self.k, rep_coe_list)
        return_element_order = el_lin.rep_linear_order()
      return return_element_order

    def make_sub_ellist_list(self, t_n, t_k, t_el, dim_list_index_ii):
      i_list = []
      j_list = []
      sub_ellist_list = []
      sub_el_coelist_list = []
      return_sub_ref_list = []
      break_flag = False

      if self.is_rep_element()[0] == False:

        t_i_el_sus_element = self.sus_element()
        t_i_el_has_relation = self.has_relation()

        if t_el == [1]:
          pass
        elif t_i_el_sus_element[4] != []:
          if t_i_el_sus_element[1] != []:
            return_sub_ref_list.append(', \ '.join(t_i_el_sus_element[1]))
          else:
            return_sub_ref_list.append('')
          sub_rep_coe = t_i_el_sus_element[4][-1]
          sub_el_lin = ElementLinear(t_n, t_k, sub_rep_coe)
          sub_el_lin_linear_to_el_list = sub_el_lin.linear_to_el_list()

          if sub_el_lin_linear_to_el_list[0] == []:
            break_flag = True
          i_list.append(dim_list_index_ii)
          j_list.append(len(t_el))
          sub_ellist_list.append(sub_el_lin_linear_to_el_list[0])
          sub_el_coelist_list.append(sub_el_lin_linear_to_el_list[1])
            
        elif t_i_el_has_relation[0]:
          sub_rep_coe = t_i_el_has_relation[1]
          return_sub_ref_list.append(t_i_el_has_relation[2])
          sub_el_lin = ElementLinear(t_n, t_k, sub_rep_coe)
          sub_el_lin_linear_to_el_list = sub_el_lin.linear_to_el_list()

          if sub_el_lin_linear_to_el_list[0] == []:
            break_flag = True
          i_list.append(dim_list_index_ii)
          j_list.append(len(t_el))
          sub_ellist_list.append(sub_el_lin_linear_to_el_list[0])
          sub_el_coelist_list.append(sub_el_lin_linear_to_el_list[1])

      return i_list, j_list, sub_ellist_list, sub_el_coelist_list, return_sub_ref_list, break_flag

    def total_coe_times_sub_comp(self):
      return_sub_tex_list = []
      return_sub_ref_list = []
      return_coe_list = []
      flag = False

      #########################################################
      el1_el_coe_out = self.el_coe_out()
      ellist2 = el1_el_coe_out[0]
      total_coe2 = el1_el_coe_out[2] * self.total_coe
      rep_coe_list2 = el1_el_coe_out[1]

      el2 = Element(self.n, ellist2, rep_coe_list2, total_coe2)
      el2_element_to_linear_coe = el2.element_to_linear_coe()
      el2_dim_list = el2.dim_list()
      if el2_element_to_linear_coe != []:
        hg2 = HomotopyGroup(self.n, self.k)
        return_sub_tex_list.append(hg2.rep_linear_tex(el2_element_to_linear_coe, total_coe2))
      else:
        return_sub_tex_list.append(el2.tex())
      
      #########################################################

      if total_coe2 >= 2:
        el1_el_coe_out = self.el_coe_out()
        return_sub_ref_list.append('(2.1), \ k(\\alpha\\beta)=\\alpha(k\\beta)' 
            + ', \ k(\\alpha\Sigma\\beta)=(k\\alpha)\Sigma\\beta'
            + ', \ \ Lem4.5, \ (k\iota_{n-1})\\beta = k\\beta \ for \ \\beta \in \pi_{i-1}(S^{n-1})'
            + ', \ n = 2, 4, 8' )
      else:
        return_sub_tex_list.pop(-1) 
      for i in range(len(ellist2)):
        for j in range(1, len(ellist2)-i+1):
          (ellist3, rep_coe_list3) = el2.sub_comp(i, j)
          n3 = el2_dim_list[i]
          k3 = el2_dim_list[i+j] - el2_dim_list[i]
          sub_el3 = Element(n3, ellist3, rep_coe_list3)
          sub_el3_total_coe_to_sub_comp_ij = sub_el3.total_coe_to_sub_comp(i, j)
          sub_el3_element_order = sub_el3.element_order()
          sub_el3_tex = sub_el3.tex()
          sub_hg3 = HomotopyGroup(n3, k3)
          sub_hg3_group_order = sub_hg3.group_order()

          try:
            if sub_el3_total_coe_to_sub_comp_ij and total_coe2 % sub_el3_element_order == 0:
              return_sub_tex_list.append('0')
              if sub_el3_element_order == 1:
                return_sub_ref_list.append(f'{sub_el3_tex} = 0')
              else:
                return_sub_ref_list.append(f'{sub_el3_element_order} {sub_el3_tex} = 0')
          except:
            pass
          try:
            if sub_el3_total_coe_to_sub_comp_ij and total_coe2 % sub_hg3_group_order == 0:
              return_sub_tex_list.append('0')
              return_sub_ref_list.append(f'{sub_hg3_group_order} \pi_{ {n3}+{k3} }^{n3} = 0')
            else:
              pass
          except:
            pass
          if len(return_sub_tex_list) >= 2:
            try:
              if return_sub_tex_list[-1] == return_sub_tex_list[-2]:
                return_sub_tex_list.pop(-1)
                return_sub_ref_list.pop(-1)
            except IndexError:
              pass
          if '0' in return_sub_tex_list:
            hg = HomotopyGroup(self.n, self.k)
            return_coe_list = [0] * hg.direct_sum()
            flag = True
            break
        if flag:
          break

      return return_sub_tex_list, return_sub_ref_list, return_coe_list, flag

    def total_coe_times_sub_comp_is_zero(self, totalcoe=1):
      return_sub_tex_list = []
      return_sub_ref_list = []
      return_coe_list = []
      flag = False
      for t in range(2**(len(self.ellist)-1)):
        (t_n_list, t_k_list, t_el_list, t_el_coe_list) = self.sub_comp_list(t)
        i_list = []
        j_list = []
        sub_ellist_list = []
        sub_el_coelist_list = []
        for ii, t_n, t_k, t_el, t_el_coe in zip(range(len(t_el_list)), 
          t_n_list, t_k_list, t_el_list, t_el_coe_list):
          dim_list_index_ii = self.dim_list().index(t_n_list[ii])
          t_i_el = Element(t_n, t_el, t_el_coe)

          t_i_el_make_sub_ellist_list = \
            t_i_el.make_sub_ellist_list(t_n, t_k, t_el, dim_list_index_ii)
          i_list.extend(t_i_el_make_sub_ellist_list[0])
          j_list.extend(t_i_el_make_sub_ellist_list[1])
          sub_ellist_list.extend(t_i_el_make_sub_ellist_list[2])
          sub_el_coelist_list.extend(t_i_el_make_sub_ellist_list[3])
          return_sub_ref_list.extend(t_i_el_make_sub_ellist_list[4])
          break_flag = t_i_el_make_sub_ellist_list[5]
          if break_flag:
            break

        change_el_list_list = self.change_el_list_list(i_list, j_list, sub_ellist_list, sub_el_coelist_list)
        ellist1 = change_el_list_list[0]
        el_coelist1 = change_el_list_list[1]
        el1 = Element(self.n, ellist1, el_coelist1, totalcoe)

        if i_list != []:
          return_sub_tex_list.append(el1.tex())

        el1_total_coe_times_sub_comp = el1.total_coe_times_sub_comp()
        return_sub_tex_list.extend(el1_total_coe_times_sub_comp[0])
        return_sub_ref_list.extend(el1_total_coe_times_sub_comp[1])
        return_coe_list.extend(el1_total_coe_times_sub_comp[2])
        flag = el1_total_coe_times_sub_comp[3]
        
        if flag:
          break

      return return_sub_tex_list, return_sub_ref_list, return_coe_list

    def change_first_dim(self, first_dim):
      n = self.n
      dim_list = self.dim_list()
      if first_dim == 'first_element' or len(dim_list) == 1:
        gen_query = f'select * from gen where id = {self.ellist[0]}'
        c.execute(gen_query)
        n = c.fetchone()['n']
      elif first_dim == 'second_element':
        try:
          gen_query = f'select * from gen where id = {self.ellist[1]}'
          for row in c.execute(gen_query):
            n = dim_list[0] - dim_list[1] + row['n']
        except IndexError:
          gen_query = f'select * from gen where id = {self.ellist[0]}'
          c.execute(gen_query)
          n = c.fetchone()['n']
      return n

    def deformation_relation(self, coe_list0):
      hg = HomotopyGroup(self.n, self.k)
      hg_group_is_zero = hg.group_is_zero()
      hg_direct_sum = hg.direct_sum()
      relation_tex_list = []
      reference_tex_list = []
      return_coe_list = []
      el_list1 = [el for el in self.ellist]
      coe_list1 = [coe for coe in self.el_coelist]
      (selfellist, selfel_coelist, selftotal_coe) = hg.el_coe_out(el_list1, coe_list1)
      selftotal_coe = selftotal_coe * self.total_coe

      coeout_el = Element(self.n, selfellist, selfel_coelist, selftotal_coe)
      coeout_is_rep_element = coeout_el.is_rep_element()
      coeout_el_include_EP = coeout_el.include_EP()
      coeout_el_has_relation = coeout_el.has_relation()
      coeout_el_has_sus_relation_selftotal_coe = coeout_el.has_sus_relation(selftotal_coe)
      coeout_el_is_P_image = coeout_el.is_P_image()

      # case with elemets include zero
      if 0 in selfellist:
        relation_tex_list.append('0')
        reference_tex_list.append('')
        return_coe_list = [0]

      # case with group is zero
      elif hg_group_is_zero:
        relation_tex_list.append('0')
        reference_tex_list.append(f'\pi_{ {self.n+self.k} }^{ {self.n} }=0')
        return_coe_list = [0]

      # case with representation element
      elif hg_group_is_zero == False and coeout_is_rep_element[0]:
        relation_tex_list.append(hg.rep_linear_tex(coeout_is_rep_element[2], selftotal_coe))
        gencoe_list = [coe * total_coe for coe in coeout_is_rep_element[2]]
        return_coe_list = hg.mod_gen_coe_list(gencoe_list)
        reference_tex_list.append(f'(Generator)')

      # case with include EP
      elif coeout_el_include_EP:
        relation_tex_list.append('0')
        reference_tex_list.append('\Sigma P=0')
        return_coe_list = [0 for i in range(hg_direct_sum)]

      # case with group include subcomposition is zero
      elif hg_group_is_zero == False and coeout_el_include_EP == False and len(selfellist) >= 2:
        for t in range(2**(len(selfellist)-1)):
          (t_n_list, t_k_list, t_el_list, t_el_coe_list) = hg.sub_comp_list(selfellist, selfel_coelist, t)
          for i in range(len(t_n_list)):
            t_i_hg = HomotopyGroup(t_n_list[i], t_k_list[i])
            t_i_el = Element(t_n_list[i], t_el_list[i])
            t_i_el_composition_is_zero = t_i_el.composition_is_zero()
            if t_i_hg.group_is_zero():
              relation_tex_list.append('0')
              el_tex = t_i_el.tex()
              reference_tex_list.append(f'{el_tex} \in \pi_{ {t_n_list[i] + t_k_list[i]} }^{ {t_n_list[i]} }=0')
              return_coe_list = [0 for i in range(hg_direct_sum)]
            if t_i_el_composition_is_zero and t_i_el_composition_is_zero[1] != '':
              relation_tex_list.append(f'0')
              reference_tex_list.append(t_i_el_composition_is_zero[2])
              return_coe_list = [0 for i in range(hg_direct_sum)]

      # case with suspension of representation element
      if hg_group_is_zero == False and coeout_el_include_EP == False and '0' not in relation_tex_list and return_coe_list == []:
        coeout_el_sus_element_selftotal_coe = coeout_el.sus_element(selftotal_coe)
        for relation, reference in zip(coeout_el_sus_element_selftotal_coe[0], coeout_el_sus_element_selftotal_coe[1]):
          if relation not in relation_tex_list \
          or reference not in reference_tex_list:
            relation_tex_list.append(relation)
            reference_tex_list.append(reference)
            return_coe_list = coeout_el_sus_element_selftotal_coe[4][-1]

      # case with relation
      if coeout_el_has_relation[0] and return_coe_list == []:
        hg_rep_linear_tex_coeout_el_has_relation_selftotal_coe = hg.rep_linear_tex(coeout_el_has_relation[1], selftotal_coe)
        if hg_rep_linear_tex_coeout_el_has_relation_selftotal_coe not in relation_tex_list \
        or coeout_el_has_relation[2] not in reference_tex_list:
          relation_tex_list.append(hg_rep_linear_tex_coeout_el_has_relation_selftotal_coe)
          reference_tex_list.append(coeout_el_has_relation[2])
          return_coe_list = [coe * selftotal_coe for coe in coeout_el_has_relation[1]]

      # case with suspension of relation 
      if hg_group_is_zero == False and coeout_el_include_EP == False and '0' not in relation_tex_list and return_coe_list == []:
        for relation, reference in zip(coeout_el_has_sus_relation_selftotal_coe[0], coeout_el_has_sus_relation_selftotal_coe[1]):
          if relation not in relation_tex_list \
          or reference not in reference_tex_list:
            relation_tex_list.append(relation)
            reference_tex_list.append(reference)
            return_coe_list = coeout_el_has_sus_relation_selftotal_coe[4][-1]

      # case with P-image
      if selfellist != []:
        if coeout_el_is_P_image[0] and len(selfellist) >= 2:
          if len(coeout_el_is_P_image[3]) > len(selfel_coelist):
            coe_list = [1] * (len(coeout_el_is_P_image[3]) - len(selfel_coelist)) + selfel_coelist
          else:
            coe_list = selfel_coelist

          P_total_coe = np.prod(coe_list0)
          P_inverse_n = coeout_el_is_P_image[1]
          P_inverse_k = coeout_el_is_P_image[2]
          P_inverse_el_list = hg.delete_iota(coeout_el_is_P_image[3], coe_list)[0]
          P_inverse_hg = HomotopyGroup(P_inverse_n, P_inverse_k)
          P_inverse_el = Element(P_inverse_n, P_inverse_el_list)
          P_inverse_el_element_to_id = P_inverse_el.element_to_id()
          P_inverse_hg_P_coe_P_inverse_el_element_to_id = P_inverse_hg.P_coe(P_inverse_el_element_to_id[1])
          P_image_coe = P_inverse_hg_P_coe_P_inverse_el_element_to_id[0]
          P_inverse_el_tex = P_inverse_el.tex()
          if P_total_coe == 1:
            relation_tex_list.append(f'P( {P_inverse_el_tex} )')
            return_coe_list = P_image_coe
          else:
            relation_tex_list.append(f'{P_total_coe} P( {P_inverse_el_tex} )')
            return_coe_list = [i * total_coe for i in P_image_coe]
          
          reference_tex_list.append('Prop2.5, \ P(\\alpha\Sigma^2 \\beta)=P(\\alpha)\\beta')
          relation_tex_list.append(hg.rep_linear_tex(P_image_coe, P_total_coe))
          reference_tex_list.append(P_inverse_hg_P_coe_P_inverse_el_element_to_id[1])
    
        # case with total_coe_times_sub_comp_is_zero
        if reference_tex_list == [] and return_coe_list == []:
          if '0' not in relation_tex_list:
            coeout_el_total_coe_times_sub_comp_is_zero_selftotal_coe = \
              coeout_el.total_coe_times_sub_comp_is_zero(selftotal_coe)
            relation_tex_list.extend(coeout_el_total_coe_times_sub_comp_is_zero_selftotal_coe[0])
            reference_tex_list.extend(coeout_el_total_coe_times_sub_comp_is_zero_selftotal_coe[1])
            return_coe_list = coeout_el_total_coe_times_sub_comp_is_zero_selftotal_coe[2]

      else:
        relation_tex_list.append(f'{selftotal_coe} \iota_{n}')

      return relation_tex_list, reference_tex_list, return_coe_list

  class WhiteheadProduct: 
    def __init__(self, n, symbollist, ellist=[1], coelist=[1]*6):
      self.n = n
      self.symbollist = symbollist
      self.ellist = ellist
      self.coelist = coelist[:len(ellist)]

    def ellist_to_wp_ellist(self):
      wp_ellist = [[], [], [], []]
      j = 0
      for i, elem in enumerate(self.ellist):
        if self.symbollist[i] == ' ':
          wp_ellist[j].append(elem)
        else:
          j = j+1
          wp_ellist[j].append(elem)
      return wp_ellist

    def coelist_to_wp_coelist(self):
      wp_coelist = [[], [], [], []]
      j = 0
      for i, coe in enumerate(self.coelist):
        if self.symbollist[i] == ' ':
          wp_coelist[j].append(coe)
        else:
          j = j+1
          wp_coelist[j].append(coe)
      return wp_coelist

    def wp_k(self):
      wp_ellist = self.ellist_to_wp_ellist()
      return_k = n + k_dim(wp_ellist[0]) + k_dim(self.ellist) - 1
      return return_k

    def wp_dim_list(self):
      return_wp_dim_list = []
      wp_ellist = self.ellist_to_wp_ellist()
      for j in range(6):
        if j == 0:
          return_wp_dim_list.append(self.n)
        elif j == 1:
          el = Element(self.n, wp_ellist[0])
          # el_dim_list = el.el_dim_list()
          return_wp_dim_list.append(return_wp_dim_list[0] + el.k)
        elif j == 2 or j == 3:
          # print(f'return_wp_dim_list = {return_wp_dim_list}')
          if len(wp_ellist) < j:
            return_wp_dim_list.append(return_wp_dim_list[1])
          else:
            el = Element(return_wp_dim_list[j-1], wp_ellist[j-1])
            return_wp_dim_list.append(return_wp_dim_list[1] + el.k)
        elif j == 4:
          return_wp_dim_list.append(return_wp_dim_list[2] + return_wp_dim_list[3] - 1)
        else:
          wp_k = self.wp_k()
          return_wp_dim_list.append(self.n + wp_k)
      return return_wp_dim_list

    def tex(self):
      return_tex = ''
      wp_dim_list = self.wp_dim_list()
      wp_ellist = self.ellist_to_wp_ellist()
      wp_coelist = self.coelist_to_wp_coelist()
      for j in range(4):
        if j == 1:
          return_tex = return_tex + ' [ '
        elif j == 2:
          return_tex = return_tex + ', '
        elif j == 3:
          return_tex = return_tex + ' ] '
        if j == 0 or j == 1:
          el = Element(wp_dim_list[j], wp_ellist[j], wp_coelist[j])
        elif j == 2:
          el = Element(wp_dim_list[1], wp_ellist[2], wp_coelist[2])
        else:
          el = Element(wp_dim_list[4], wp_ellist[3], wp_coelist[3])
        return_tex = return_tex + el.tex()
      return return_tex

    def wp_ellist_to_ellist(self):
      return_ellist = []
      return_coelist = []
      wp_ellist = self.ellist_to_wp_ellist()
      wp_coelist = self.coelist_to_wp_coelist()
      wp_dim_list = self.wp_dim_list()
      P_dict = {6:5, 10:13, 12:17, 14:22, 16:31, 18:41, 20:53, 21:66, 22:68, 24:87, 26:116, 28:143, 30:164, 32:195}
      if wp_dim_list[1] in P_dict:
        return_ellist = wp_ellist[0]
        return_coelist = wp_coelist[0]
        return_ellist.append(P_dict[wp_dim_list[1]])
        return_coelist.append(1)
        for i in range(1,4):
          return_ellist.extend(wp_ellist[i])
          return_coelist.extend(wp_coelist[i])
      return return_ellist, return_coelist

  class TodaBracket: 
    def __init__(self, n, tt, symbollist, ellist=[1], coelist=[1]*6):
      self.n = n
      self.tt = tt
      self.symbollist = symbollist
      self.ellist = ellist
      self.coelist = coelist[:len(ellist)]

      self.k = k_dim(ellist) + 1

    def included_group(self):
      return 

    def ellist_to_tb_ellist(self):
      if self.symbollist.count(',') == 2:
        tb_ellist = [[], [], [], [], []]
      elif self.symbollist.count(',') == 3:
        tb_ellist = [[], [], [], [], [], []]
      j = 0
      for i, elem in enumerate(self.ellist):
        if self.symbollist[i] == ' ':
          tb_ellist[j].append(elem)
        else:
          j = j+1
          tb_ellist[j].append(elem)
      return tb_ellist

    def coelist_to_tb_coelist(self):
      if self.symbollist.count(',') == 2:
        tb_coelist = [[], [], [], [], []]
      elif self.symbollist.count(',') == 3:
        tb_coelist = [[], [], [], [], [], []]
      j = 0
      for i, coe in enumerate(self.coelist):
        if self.symbollist[i] == ' ':
          tb_coelist[j].append(coe)
        else:
          j = j+1
          tb_coelist[j].append(coe)
      return tb_coelist

    def tb_el_count_list(self):
      return_tb_el_count_list = [len(self.ellist_to_tb_ellist()[i]) for i in range(5)]
      return return_tb_el_count_list

    def tb_dim_list(self):
      return_tb_dim_list = []
      tb_ellist = self.ellist_to_tb_ellist()
      if self.symbollist.count(',') == 2:
        for j in range(6):
          el = Element(self.n, tb_ellist[j-1])
          el_dim_list = el.el_dim_list()
          if j == 0:
            return_tb_dim_list.append(self.n)
          elif j <= 3 or j == 5:
            return_tb_dim_list.append(return_tb_dim_list[j-1] + el_dim_list[-1] - el_dim_list[0])
          else:
            return_tb_dim_list.append(return_tb_dim_list[j-1] + el_dim_list[-1] - el_dim_list[0] + 1)
      elif self.symbollist.count(',') == 3:
        for j in range(7):
          el = Element(self.n, tb_ellist[j-1])
          el_dim_list = el.el_dim_list()
          if j == 0:
            return_tb_dim_list.append(self.n)
          elif j <= 4 or j == 6:
            return_tb_dim_list.append(return_tb_dim_list[j-1] + el_dim_list[-1] - el_dim_list[0])
          else:
            return_tb_dim_list.append(return_tb_dim_list[j-1] + el_dim_list[-1] - el_dim_list[0] + 1)

      return return_tb_dim_list

    def tb_ellist_to_ellist_str(self):
      ellist_str_list = []
      if self.symbollist.count(',') == 2:
        for i in range(1,4):
          ellist_str_list.append(' '.join(map(str, self.ellist_to_tb_ellist()[i])))
      elif self.symbollist.count(',') == 3:
        for i in range(1,5):
          ellist_str_list.append(' '.join(map(str, self.ellist_to_tb_ellist()[i])))
      return_tb_ellist_to_ellist_str = ' , '.join(ellist_str_list)
      return return_tb_ellist_to_ellist_str

    def tb_coelist_to_coelist_str(self):
      coelist_str_list = []
      if self.symbollist.count(',') == 2:
        for i in range(1,4):
          coelist_str_list.append(' '.join(map(str, self.coelist_to_tb_coelist()[i])))
      elif self.symbollist.count(',') == 3:
        for i in range(1,5):
          coelist_str_list.append(' '.join(map(str, self.coelist_to_tb_coelist()[i])))
      return_tb_coelist_to_coelist_str = ' , '.join(coelist_str_list)
      return return_tb_coelist_to_coelist_str

    def include_element_list(self):
      return_include_element_list = []
      ellist_str = self.tb_ellist_to_ellist_str()
      coelist_str = self.tb_coelist_to_coelist_str()
      query_tb_count = f'select count( * ) from TBtable where \
        element = "{ellist_str}" and coefficient = "{coelist_str}"'
      for row in c.execute(query_tb_count):
        if row['count( * )'] >=1:
          query_tb = f'select * from TBtable where \
            element = "{ellist_str}" and coefficient = "{coelist_str}"'
          for row_tb in c.execute(query_tb):
            if self.n >= row_tb['n'] and self.tt <= row_tb['tt']+self.n-row_tb['n']:
              return_include_element_list = list(map(int, row_tb['include'].split()))
      return return_include_element_list

    def tex(self):
      return_tex = ''
      tb_dim_list = self.tb_dim_list()
      tb_ellist = self.ellist_to_tb_ellist()
      tb_coelist = self.coelist_to_tb_coelist()
      if self.symbollist.count(',') == 2:
        for j in range(5):
          if j == 1:
            return_tex = return_tex + ' \{ '
          elif j == 2 or j == 3:
            return_tex = return_tex + ', '
          elif j == 4:
            if tt == 0:
              return_tex = return_tex + ' \} '
            else:
              return_tex = return_tex + ' \}_{' + f'{tt}' + '} '
          el = Element(tb_dim_list[j], tb_ellist[j], tb_coelist[j])
          return_tex = return_tex + el.tex()
      elif self.symbollist.count(',') == 3:
        for j in range(6):
          if j == 1:
            return_tex = return_tex + ' \{ '
          elif j == 2 or j == 3 or j == 4:
            return_tex = return_tex + ', '
          elif j == 5:
            if tt == 0:
              return_tex = return_tex + ' \} '
            else:
              return_tex = return_tex + ' \}_{' + f'{tt}' + '} '
          el = Element(tb_dim_list[j], tb_ellist[j], tb_coelist[j])
          return_tex = return_tex + el.tex()

      return return_tex

    def well_defined(self):
      print('well defined method')
      tb_ellist = self.ellist_to_tb_ellist()
      tb_coelist = self.coelist_to_tb_coelist()
      tb_dim_list = self.tb_dim_list()
      el_count_list = self.tb_el_count_list()
      coe_list0 = self.coelist

      tb_ellist1 = tb_ellist[1] + tb_ellist[2]
      tb_ellist2 = tb_ellist[2] + tb_ellist[3]
      tb_coelist1 = tb_coelist[1] + tb_coelist[2]
      tb_coelist2 = tb_coelist[2] + tb_coelist[3]
      el1 = Element(tb_dim_list[1], tb_ellist1, tb_coelist1)
      el2 = Element(tb_dim_list[2] - tt, tb_ellist2, tb_coelist2)
      well_def1 = el1.tex()
      well_def2 = el2.tex()
      len_coe_list0 = len(coe_list0)

      well_def1_coe_list0 = [coe_list0[i] for i in range(len_coe_list0) 
        if el_count_list[0] <= i 
        and i < el_count_list[0]+el_count_list[1]+el_count_list[2]]
      hg_well_def1 = HomotopyGroup(tb_dim_list[1], tb_dim_list[3] - tb_dim_list[1])
      deformation_relation1 = el1.deformation_relation(well_def1_coe_list0)
      well_def1_relation = hg_well_def1.rep_linear_tex(deformation_relation1[2])
      if deformation_relation1[1] == []:
        well_def1_reference = []
      else:
        well_def1_reference = deformation_relation1[1][0]

      well_def2_coe_list0 = [coe_list0[i] for i in range(len_coe_list0) 
        if el_count_list[0]+el_count_list[1] <= i 
        and i < el_count_list[0]+el_count_list[1]+el_count_list[2]+el_count_list[3]]
      hg_well_def2 = HomotopyGroup(tb_dim_list[2] - tt, tb_dim_list[4] - tb_dim_list[2] - 1)
      deformation_relation2 = el2.deformation_relation(well_def2_coe_list0)
      well_def2_relation = hg_well_def2.rep_linear_tex(deformation_relation2[2])

      if deformation_relation2[1] == []:
        well_def2_reference = []
      else:
        well_def2_reference = deformation_relation2[1][0]

      if deformation_relation2[1] == []:
        well_def2_reference = []
      else:
        well_def2_reference = deformation_relation2[1][0]
      return well_def1, well_def2, well_def1_relation, well_def2_relation \
        , well_def1_reference, well_def2_reference, deformation_relation1, deformation_relation2

    def coset(self):
      coset1 = ''
      coset2 = ''
      tb_ellist = self.ellist_to_tb_ellist()
      tb_coelist = self.coelist_to_tb_coelist()
      tb_dim_list = self.tb_dim_list()
      
      el1 = Element(tb_dim_list[0], tb_ellist[0]+tb_ellist[1], tb_coelist[0]+tb_coelist[1])
      if self.symbollist.count(',') == 2:
        el2 = Element(tb_dim_list[5], tb_ellist[4], tb_coelist[4])
      elif self.symbollist.count(',') == 3:
        el2 = Element(tb_dim_list[6], tb_ellist[5], tb_coelist[5])

      if len(el1.ellist) == 1 and el1.el_coelist != [1]:
        coset1 = f'({el1.tex()})'
      else:
        coset1 = el1.tex()

      if self.symbollist.count(',') == 2:
        if self.tt == 0:
          coset1 = coset1 \
            + f' \pi_{ {tb_dim_list[5]} }^{ {tb_dim_list[2]} } '
          hg1 = HomotopyGroup(tb_dim_list[2], tb_dim_list[5]-tb_dim_list[2])
        elif self.tt == 1:
          coset1 = coset1 \
            + f' \Sigma\pi_{ {tb_dim_list[5]-1} }^{ {tb_dim_list[2]-1} } '
          hg1 = HomotopyGroup(tb_dim_list[2]-1, tb_dim_list[5]-tb_dim_list[2])
        else:
          coset1 = coset1 \
            + f' \Sigma^{ {self.tt} }\pi_{ {tb_dim_list[5]-self.tt} }^{ {tb_dim_list[2]-self.tt} } '
          hg1 = HomotopyGroup(tb_dim_list[2]-self.tt, tb_dim_list[5]-tb_dim_list[2])
      elif self.symbollist.count(',') == 3:
        if self.tt == 0:
          coset1 = coset1 \
            + f' \pi_{ {tb_dim_list[5]+1} }^{ {tb_dim_list[2]} } '
          hg1 = HomotopyGroup(tb_dim_list[2], tb_dim_list[5]-tb_dim_list[2]+1)
        elif self.tt == 1:
          coset1 = coset1 \
            + f' \Sigma\pi_{ {tb_dim_list[5]} }^{ {tb_dim_list[2]-1} } '
          hg1 = HomotopyGroup(tb_dim_list[2]-1, tb_dim_list[5]-tb_dim_list[2]+1)
        else:
          coset1 = coset1 \
            + f' \Sigma^{ {self.tt} }\pi_{ {tb_dim_list[5]-self.tt+1} }^{ {tb_dim_list[2]-self.tt} } '
          hg1 = HomotopyGroup(tb_dim_list[2]-self.tt, tb_dim_list[5]-tb_dim_list[2]+1)
      
      if len(el2.ellist) == 1 and el2.el_coelist != [1]:
        coset1 = coset1 + f'({el2.tex()})'
      else:
        coset1 = coset1 + el2.tex()
      coset_pi1 = hg1.pi_tex()
      coset_pi_tex1 = hg1.group_structure()

      coset_gen_list1 = []
      coset_pi_gen_list1 = []
      direct_sum1 = hg1.direct_sum()
      for id in range(direct_sum1):
        hg1_rep_list = hg1.rep_list(id)
        coset_pi_gen_list1.append(hg1.el_tex(hg1_rep_list))

        if self.symbollist.count(',') == 2:
          coset_ellist1 = tb_ellist[0]+tb_ellist[1]+hg1_rep_list+tb_ellist[4]
          coset_coelist1 = tb_coelist[0]+tb_coelist[1]+[1]*len(hg1_rep_list)+tb_coelist[4]
        elif self.symbollist.count(',') == 3:
          coset_ellist1 = tb_ellist[0]+tb_ellist[1]+hg1_rep_list+tb_ellist[5]
          coset_coelist1 = tb_coelist[0]+tb_coelist[1]+[1]*len(hg1_rep_list)+tb_coelist[5]

        coset_el1 = Element(self.n, coset_ellist1, coset_coelist1)
        coset_el1_deformation_relation_coset_coelist1 = coset_el1.deformation_relation(coset_coelist1)
        if coset_el1_deformation_relation_coset_coelist1[0] != []:
          coset_gen1 = coset_el1_deformation_relation_coset_coelist1[0][-1]
        else:
          coset_gen1 = coset_el1.tex()
        coset_gen_list1.append(coset_gen1)

      coset_gen_tex_list1 = [' \{ ' + gen + ' \} ' for gen in coset_gen_list1]
      coset_tex1 = ' + '.join(coset_gen_tex_list1)

      el3 = Element(tb_dim_list[0], tb_ellist[0], tb_coelist[0])
      if self.symbollist.count(',') == 2:
        el4 = Element(tb_dim_list[3]+1, tb_ellist[3]+tb_ellist[4], tb_coelist[3]+tb_coelist[4])
      elif self.symbollist.count(',') == 3:
        el4 = Element(tb_dim_list[4]+2, tb_ellist[4]+tb_ellist[5], tb_coelist[4]+tb_coelist[5])

      if len(el3.ellist) == 1 and el3.el_coelist != [1]:
        coset2 = f'({el3.tex()})'
      else:
        coset2 = el3.tex()

      if self.symbollist.count(',') == 2:
        coset2 = coset2 \
          + f' \pi_{ {tb_dim_list[3]+1} }^{ {tb_dim_list[1]} } ' 
      elif self.symbollist.count(',') == 3:
        coset2 = coset2 \
          + f' \pi_{ {tb_dim_list[3]+2} }^{ {tb_dim_list[1]} } ' 
      
      if len(el4.ellist) == 1 and el4.el_coelist[0] != 1:
        coset2 = coset2 + f'({el4.tex()})'
      else:
        coset2 = coset2 + el4.tex()

      coset_gen_list2 = []
      if self.symbollist.count(',') == 2:
        hg2 = HomotopyGroup(tb_dim_list[1], tb_dim_list[3]-tb_dim_list[1]+1)
      elif self.symbollist.count(',') == 3:
        hg2 = HomotopyGroup(tb_dim_list[1], tb_dim_list[3]-tb_dim_list[1]+2)

      coset_pi2 = hg2.pi_tex()
      coset_pi_tex2 = hg2.group_structure()
      direct_sum2 = hg2.direct_sum()
      for id in range(direct_sum2):
        hg2_rep_list = hg2.rep_list(id)

        if self.symbollist.count(',') == 2:
          coset_ellist2 = tb_ellist[0]+hg2_rep_list+tb_ellist[3]+tb_ellist[4]
          coset_coelist2 = tb_coelist[0]+[1]*len(hg2_rep_list)+tb_coelist[3]+tb_coelist[4]
        elif self.symbollist.count(',') == 3:
          coset_ellist2 = tb_ellist[0]+hg2_rep_list+tb_ellist[3]+tb_ellist[4]+tb_ellist[5]
          coset_coelist2 = tb_coelist[0]+[1]*len(hg2_rep_list)+tb_coelist[3]+tb_coelist[4]+tb_coelist[5]
        
        coset_el2 = Element(self.n, coset_ellist2, coset_coelist2)
        coset_el2_deformation_relation_coset_coelist2 = coset_el2.deformation_relation(coset_coelist2)
        if coset_el2_deformation_relation_coset_coelist2[0] != []:
          coset_gen2 = coset_el2_deformation_relation_coset_coelist2[0][-1]
        else:
          coset_gen2 = coset_el2.tex()
        coset_gen_list2.append(coset_gen2)

      coset_gen_tex_list2 = [' \{ ' + gen + ' \} ' for gen in coset_gen_list2]
      coset_tex2 = ' + '.join(coset_gen_tex_list2)

      return coset1, coset2, coset_tex1, coset_tex2, coset_pi1, coset_pi2, coset_pi_tex1, coset_pi_tex2


  coe_list0 = [int(request.form[f'coe_list[{i}]']) for i in range(6)]

  displays = [request.form[f'displays[{i}]'] for i in range(6)]
  el_list0 = [el_id(display) for display in displays if display != ' ']

  symbols0 = [request.form[f'symbols0[{i}]'] for i in range(7)]

  if '{' in symbols0:
    tb = TodaBracket(n, tt, symbols0, el_list0, coe_list0)
  elif '[' in symbols0:
    wp = WhiteheadProduct(n, symbols0, el_list0, coe_list0)
    wp_ellist = wp.ellist_to_wp_ellist()
    wp_coelist = wp.coelist_to_wp_coelist()
    wp_dimlist = wp.wp_dim_list()
    wp_k = wp.wp_k()
    wp_change_ellist = wp.wp_ellist_to_ellist()

  k = k_dim(el_list0)

  # first_dim = 'dim'
  first_dim = request.form['first_dim']

  display_mode = request.form['display_mode']
  # display_mode = 'relation'

  hg0 = HomotopyGroup(n, k)
  el0 = Element(n, el_list0)

  n = el0.change_first_dim(first_dim)
  if '{' in symbols0:
    k = k + 1
  elif '[' in symbols0:
    wp = WhiteheadProduct(n, symbols0, el_list0, coe_list0)
    k = wp.wp_k()
  hg = HomotopyGroup(n, k)

  (el_list, coe_list) = hg.delete_iota(el_list0, coe_list0)

  if '{' in symbols0:
    tb = TodaBracket(n, tt, symbols0, el_list0, coe_list0)
    disp0 = tb.tex()
  elif '[' in symbols0:
    wp = WhiteheadProduct(n, symbols0, el_list0, coe_list0)
    disp0 = wp.tex()
  else:
    disp0 = hg.el_coe_tex(el_list, coe_list)

  # case with Hopf map
  for i, elem in enumerate(el_list):
    if elem in {2,4,9} and i >= 1 and hg.el_sus_list(el_list)[i] == 0:
      if el_list[i-1] == 1:
        coe_list[i] = coe_list[i] * coe_list[i-1] ** 2
        coe_list[i-1] = 1

  el_list1 = el_list
  coe_list1 = coe_list
  (el_list, coe_list, total_coe) = hg.el_coe_out(el_list1, coe_list1)

  relation_tex_list = []
  reference_tex_list = []
  return_coe_list = []

  if '[' in symbols0:
    wp_el0 = Element(n, wp_ellist[0], wp_coelist[0])
    p_ellist = wp_ellist[1] + wp_ellist[2] + wp_ellist[3]
    p_coelist = wp_coelist[1] + wp_coelist[2] + wp_coelist[3]
    wp_el1 = Element(wp_dimlist[1]*2+1, p_ellist, p_coelist)
    relation_tex_list.append(f'{wp_el0.tex()} P({wp_el1.tex()})')
    reference_tex_list.append('')

    if wp_change_ellist[0] != []:
      el_wp = Element(n, wp_change_ellist[0], wp_change_ellist[1])
      relation_tex_list.append(el_wp.tex())
      reference_tex_list.append('Prop 2.5, \ P(\Sigma^2 \gamma)=\pm[\iota_m, \iota_m]\gamma')
      (deform_relation_tex_list, deform_reference_tex_list, deform_return_coe_list) \
        = el_wp.deformation_relation(wp_change_ellist[1])
      relation_tex_list.extend(deform_relation_tex_list)
      reference_tex_list.extend(deform_reference_tex_list)


  hgP = HomotopyGroup((n-1)/2, n+k-2-(n-1)/2)
  hgE = HomotopyGroup(n+1, k)
  hgH = HomotopyGroup(2*n-1, k-n+1)

  if display_mode == 'P-image':
    disp0 = f'P({disp0})'
    el1 = Element(n, el_list, coe_list)
    if el1.element_to_id()[0]:
      relation_tex_list.append(hgP.rep_linear_tex(hg.P_coe(el1.element_to_id()[1])[0], total_coe))
      reference_tex_list.append(hg.P_coe(el1.element_to_id()[1])[1])
    else:
      relation_tex_list.append('')
      reference_tex_list.append('')
  elif display_mode == 'E-image':
    disp0 = f'\Sigma({disp0})'
    el1 = Element(n, el_list, coe_list)
    if el1.element_to_id()[0]:
      if hgE.rep_linear_tex(hg.E_coe(el1.element_to_id()[1])[0]) not in relation_tex_list \
      or hg.E_coe(el1.element_to_id()[1])[1] not in relation_tex_list:
        relation_tex_list.append(hgE.rep_linear_tex(hg.E_coe(el1.element_to_id()[1])[0], total_coe))
        reference_tex_list.append(hg.E_coe(el1.element_to_id()[1])[1])
    else:
      el1 = Element(n+1, el_list, coe_list)
      for relation, reference in zip(el1.sus_element()[0], el1.sus_element()[1]):
        if relation not in relation_tex_list \
        or reference not in reference_tex_list:
          relation_tex_list.append(relation)
          reference_tex_list.append(reference)
  elif display_mode == 'H-image':
    disp0 = f'H({disp0})'
    el1 = Element(n, el_list, coe_list)
    if el1.element_to_id()[0]:
      relation_tex_list.append(hgH.rep_linear_tex(hg.H_coe(el1.element_to_id()[1])[0], total_coe))
      reference_tex_list.append(hg.H_coe(el1.element_to_id()[1])[1])
    else:
      relation_tex_list.append('')
      reference_tex_list.append('')
  elif '{' not in symbols0 and '[' not in symbols0:
    el = Element(n, el_list, coe_list, total_coe)
    (relation_tex_list, reference_tex_list, return_coe_list) = el.deformation_relation(coe_list0)

  well_def1 = ''
  well_def2 = ''
  well_def1_relation = ''
  well_def2_relation = ''
  well_def1_reference = ''
  well_def2_reference = ''
  well_def1_deformation = ''
  well_def2_deformation = ''
  coset1 = ''
  coset2 = ''
  coset_tex1 = ''
  coset_tex2 = ''
  coset_pi1 = ''
  coset_pi2 = ''
  coset_pi_tex1 = ''
  coset_pi_tex2 = ''
  include_element_tex = ''
  if '{' in symbols0:
    (coset1, coset2, coset_tex1, coset_tex2, \
      coset_pi1, coset_pi2, coset_pi_tex1, coset_pi_tex2) = tb.coset()
    (well_def1, well_def2, well_def1_relation, well_def2_relation
      , well_def1_reference, well_def2_reference
      , well_def1_deformation, well_def2_deformation) = tb.well_defined()

    if well_def1_relation == '0' and well_def2_relation == '0':
      include_element_list = tb.include_element_list()
      include_el = Element(n, include_element_list)
      include_element_tex = include_el.tex()
      include_id = include_el.element_to_id()
    
  group_tex = hg.group_structure()

  group1_tex = ''
  group1 = []

  if display_mode == 'P-image':
    if n+k-2-(n-1)/2 <= -1:
      query = f'select * from sphere where n = {0} and k = {-1}'
    elif n+k-2-(n-1)/2+2 >= (n-1)/2:
      query = f'select * from sphere where n = {(n-1)/2} and k = {n+k-2-(n-1)/2}'
    else:
      query = f'select * from sphere where n = {n+k-2-(n-1)/2+2} and k = {n+k-2-(n-1)/2}'
    for row in c.execute(query):
      if row['orders'] == 0:
        group1.append('0')
      elif row['orders'] == inf:
        group1.append('Z')
      else:
        group1.append(f"Z_{ {int(row['orders'])} }")
    group1_gen = [hgP.rep_linear_tex(hgP.gen_coe_list(j)) for j in range(hgP.direct_sum())]
    group1_tex_list = [gr + '\{' + gen + '\}' for (gr, gen) in zip(group1, group1_gen)]
    group1_tex = ' \oplus '.join(group1_tex_list)
    if well_def1_relation == '0' and well_def2_relation == '0':
      if include_id[0]:
        include_element_tex = f'P({include_element_tex})\ = ' + hg.P_image_tex(include_id[1])
  elif display_mode == 'E-image':
    if k <= -1:
      query = f'select * from sphere where n = {0} and k = {-1}'
    elif k+2 >= n+1:
      query = f'select * from sphere where n = {n+1} and k = {k}'
    else:
      query = f'select * from sphere where n = {k+2} and k = {k}'
    for row in c.execute(query):
      if row['orders'] == 0:
        group1.append('0')
      elif row['orders'] == inf:
        group1.append('Z')
      else:
        group1.append(f"Z_{ {int(row['orders'])} }")
    group1_gen = [hgE.rep_linear_tex(hgE.gen_coe_list(j)) for j in range(hgE.direct_sum())]
    group1_tex_list = [gr + '\{' + gen + '\}' for (gr, gen) in zip(group1, group1_gen)]
    group1_tex = ' \oplus '.join(group1_tex_list)
    if well_def1_relation == '0' and well_def2_relation == '0':
      if include_id[0]:
        include_element_tex = f'\Sigma({include_element_tex})\ = ' + hg.E_image_tex(include_id[1])
  elif display_mode == 'H-image':
    if k-n+1 <= -1:
      query = f'select * from sphere where n = {0} and k = {-1}'
    elif k-n+3 >= 2*n-1:
      query = f'select * from sphere where n = {2*n-1} and k = {k-n+1}'
    else:
      query = f'select * from sphere where n = {k-n+3} and k = {k-n+1}'
    for row in c.execute(query):
      if row['orders'] == 0:
        group1.append('0')
      elif row['orders'] == inf:
        group1.append('Z')
      else:
        group1.append(f"Z_{ {int(row['orders'])} }")
    group1_gen = [hgH.rep_linear_tex(hgH.gen_coe_list(j)) for j in range(hgH.direct_sum())]
    group1_tex_list = [gr + '\{' + gen + '\}' for (gr, gen) in zip(group1, group1_gen)]
    group1_tex = ' \oplus '.join(group1_tex_list)
    if well_def1_relation == '0' and well_def2_relation == '0':
      if include_id[0]:
        include_element_tex = f'H({include_element_tex})\ = ' + hg.H_image_tex(include_id[1])

  relation_count = len(relation_tex_list)

  conn.close()

  return render_template('relation.html', n=n, k=k, tt=tt \
    , display_list=display_list \
    , disp0=disp0, displays=displays, coe_list0=coe_list0 \
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
    , include_element_tex=include_element_tex  )

## おまじない
if __name__ == "__main__":
  app.run(debug=True)
  # app.run(debug=True, host='0.0.0.0', port=int(os.environ.get('PORT', 5000)))

