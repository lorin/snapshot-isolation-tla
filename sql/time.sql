-- T1 - active: 825
begin;
select pg_current_xact_id();
insert into obj (k,v) values ('1', 1);


-- T2 - commit: 826
begin;
select pg_current_xact_id();
insert into obj (k,v) values ('2', 1);
commit;


-- T3 - active: 827
begin;
select pg_current_xact_id();
insert into obj (k,v) values ('3', 1);


-- T4 - commit: 828
begin;
select pg_current_xact_id();
insert into obj (k,v) values ('4', 1);
commit;



-- T5 - active: 829
begin;
select pg_current_xact_id();
insert into obj (k,v) values ('5', 1);


-- now:830 
begin;
select pg_current_xact_id();
SELECT pg_current_snapshot();