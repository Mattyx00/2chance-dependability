package model.dao;

import model.beans.Specifiche;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.SQLException;
import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class ProdottoDAOBenchmark {

    private ProdottoDAO prodottoDAO;
    private ArrayList<Specifiche> sampleSpecifiche;

    @Setup(Level.Trial)
    public void setup() {
        this.prodottoDAO = new ProdottoDAO();
        this.sampleSpecifiche = new ArrayList<>();
        this.sampleSpecifiche.add(new Specifiche("Colore", "Nero"));
        this.sampleSpecifiche.add(new Specifiche("Memoria", "256GB"));
        this.sampleSpecifiche.add(new Specifiche("Schermo", "6.1 pollici"));
    }

    @TearDown(Level.Iteration)
    public void teardown() {
        try {
            // Delete added specs for dummy product ID 999 to keep database clean
            prodottoDAO.eliminaSpecificheProdotto(999);
        } catch (SQLException e) {
            // Ignore
        }
    }

    @Benchmark
    public void benchmarkGetProdotti(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.getProdotti());
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottoByIdValid(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.getProdottoById(3));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottoByIdNonExistent(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.getProdottoById(999));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottoByIdInvalid(Blackhole bh) {
        try {
            prodottoDAO.getProdottoById(-1);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottiByCategoriaValid(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.getProdottiByCategoria("Iphone"));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottiByCategoriaNonExistent(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.getProdottiByCategoria("NonExistent"));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottiByCategoriaInvalid(Blackhole bh) {
        try {
            prodottoDAO.getProdottiByCategoria("");
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetUltimiProdotti(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.getUltimiProdotti());
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkCercaProdottiValid(Blackhole bh) {
        try {
            bh.consume(prodottoDAO.cercaProdotti("Apple"));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkCercaProdottiInvalid(Blackhole bh) {
        try {
            prodottoDAO.cercaProdotti("");
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkAggiungiSpecifiche(Blackhole bh) {
        try {
            prodottoDAO.aggiungiSpecifiche(sampleSpecifiche, 999);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }
}
