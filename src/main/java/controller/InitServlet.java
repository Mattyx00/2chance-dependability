package controller;

import model.beans.Categoria;
import model.beans.Prodotto;
import services.InitService;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "InitServlet", value = "/InitServlet", loadOnStartup = 0)
public class InitServlet extends HttpServlet {
    private InitService initService;

    @Override
    public void init() throws ServletException {
        super.init();
        try {
            this.initService = new InitService();
            ArrayList<Categoria> categorie = initService.getCategorie();
            getServletContext().setAttribute("categorie", categorie);

            ArrayList<Prodotto> prodotti = initService.getUltimiProdotti();
            getServletContext().setAttribute("prodotti", prodotti);

        } catch (SQLException e) {
            e.printStackTrace();
            throw new ServletException("Failed to initialize InitService", e);
        }
    }
}

